-- Prove2me | solution 1 for OnlineMaxWeightMatch.Approx.proposition_2_7_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:10:29.275622+00:00
-- url     : https://prove2.me/submissions/75501fac-68b8-4eb4-a98f-665cbb4722ce

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_NegativelyAssociated

open MeasureTheory ProbabilityTheory

namespace LPM271
open OnlineMaxWeightMatch.Approx
open Classical

/-- extension by zero of a vector indexed by a finset -/
noncomputable def ext0 {κ : Type*} (S : Finset κ) (z : S → ℝ) : κ → ℝ :=
  fun i => if h : i ∈ S then z ⟨i, h⟩ else 0

lemma ext0_mono {κ : Type*} (S : Finset κ) : Monotone (ext0 S) := by
  intro z z' h i
  simp only [ext0]
  split_ifs
  · exact h _
  · exact le_rfl

lemma ext0_meas {κ : Type*} (S : Finset κ) : Measurable (ext0 S) := by
  apply measurable_pi_lambda
  intro i
  simp only [ext0]
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

lemma ext0_restrict {κ : Type*} (S : Finset κ) (u : κ → ℝ) (i : κ) (h : i ∈ S) :
    ext0 S (fun a : S => u a) i = u i := by
  simp [ext0, h]

lemma bdd_integrable {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (h : α → ℝ) (hm : Measurable h) (C : ℝ) (hC : ∀ a, |h a| ≤ C) : Integrable h ν :=
  Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun a => by rw [Real.norm_eq_abs]; exact hC a))

lemma abs_integral_le {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (h : α → ℝ) (C : ℝ) (hC : ∀ a, |h a| ≤ C) : |∫ a, h a ∂ν| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := ν) (f := h) (C := C)
    (Filter.Eventually.of_forall (fun a => by rw [Real.norm_eq_abs]; exact hC a))
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
  exact this

/-- NA transferred to the law of the random vector -/
lemma NA_law {Ω κ : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : κ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hNA : NegativelyAssociated X μ)
    (A B : Finset κ) (hAB : Disjoint A B) (f : (A → ℝ) → ℝ) (g : (B → ℝ) → ℝ)
    (hf : Monotone f) (hg : Monotone g) (hfm : Measurable f) (hgm : Measurable g)
    (hfb : ∃ C : ℝ, ∀ y, |f y| ≤ C) (hgb : ∃ C : ℝ, ∀ y, |g y| ≤ C) :
    ∫ u, f (fun a : A => u a) * g (fun b : B => u b) ∂(μ.map (fun ω i => X i ω)) ≤
      (∫ u, f (fun a : A => u a) ∂(μ.map (fun ω i => X i ω))) *
        ∫ u, g (fun b : B => u b) ∂(μ.map (fun ω i => X i ω)) := by
  have hU : Measurable (fun ω i => X i ω) := measurable_pi_lambda _ hX
  have hfA : Measurable (fun u : κ → ℝ => f (fun a : A => u a)) :=
    hfm.comp (measurable_pi_lambda _ (fun a => measurable_pi_apply _))
  have hgB : Measurable (fun u : κ → ℝ => g (fun b : B => u b)) :=
    hgm.comp (measurable_pi_lambda _ (fun b => measurable_pi_apply _))
  have hFG : Measurable (fun u : κ → ℝ => f (fun a : A => u a) * g (fun b : B => u b)) :=
    hfA.mul hgB
  rw [integral_map hU.aemeasurable hFG.aestronglyMeasurable,
    integral_map hU.aemeasurable hfA.aestronglyMeasurable,
    integral_map hU.aemeasurable hgB.aestronglyMeasurable]
  exact hNA A B hAB f g hf hg hfm hgm hfb hgb

lemma elim_meas {κ₁ κ₂ : Type*} (c : κ₁ ⊕ κ₂) :
    Measurable (fun p : (κ₁ → ℝ) × (κ₂ → ℝ) => Sum.elim p.1 p.2 c) := by
  rcases c with i | j
  · exact (measurable_pi_apply i).comp measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

end LPM271

open OnlineMaxWeightMatch.Approx LPM271 in
theorem solution {Ω κ₁ κ₂ : Type*} [MeasurableSpace Ω] [Fintype κ₁] [Fintype κ₂]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : κ₁ → Ω → ℝ) (Y : κ₂ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hindep : IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) μ)
    (hXNA : NegativelyAssociated X μ) (hYNA : NegativelyAssociated Y μ) :
    NegativelyAssociated (Sum.elim X Y) μ := by
  classical
  intro A B hAB f g hf hg hfm hgm hfb hgb
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  set U : Ω → κ₁ → ℝ := fun ω i => X i ω
  set V : Ω → κ₂ → ℝ := fun ω j => Y j ω
  have hU : Measurable U := measurable_pi_lambda _ hX
  have hV : Measurable V := measurable_pi_lambda _ hY
  set PX := μ.map U
  set PY := μ.map V
  haveI : IsProbabilityMeasure PX := Measure.isProbabilityMeasure_map hU.aemeasurable
  haveI : IsProbabilityMeasure PY := Measure.isProbabilityMeasure_map hV.aemeasurable
  have hjoint : μ.map (fun ω => (U ω, V ω)) = PX.prod PY :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).mp hindep
  have hUV : Measurable (fun ω => (U ω, V ω)) := hU.prodMk hV
  -- the test functions on the product of the two laws
  let F : (κ₁ → ℝ) × (κ₂ → ℝ) → ℝ := fun p => f (fun a : A => Sum.elim p.1 p.2 a.1)
  let G : (κ₁ → ℝ) × (κ₂ → ℝ) → ℝ := fun p => g (fun b : B => Sum.elim p.1 p.2 b.1)
  have hFm : Measurable F := hfm.comp (measurable_pi_lambda _ (fun a => elim_meas a.1))
  have hGm : Measurable G := hgm.comp (measurable_pi_lambda _ (fun b => elim_meas b.1))
  have hFb : ∀ p, |F p| ≤ Cf := fun p => hCf _
  have hGb : ∀ p, |G p| ≤ Cg := fun p => hCg _
  have hfω : ∀ ω, f (fun a : A => Sum.elim X Y a ω) = F (U ω, V ω) := by
    intro ω; simp only [F]; congr 1; funext a; rcases a with ⟨a | a, _⟩ <;> rfl
  have hgω : ∀ ω, g (fun b : B => Sum.elim X Y b ω) = G (U ω, V ω) := by
    intro ω; simp only [G]; congr 1; funext b; rcases b with ⟨b | b, _⟩ <;> rfl
  -- expectations as integrals against `PX ⊗ PY`
  have hE : ∀ h : (κ₁ → ℝ) × (κ₂ → ℝ) → ℝ, Measurable h →
      ∫ ω, h (U ω, V ω) ∂μ = ∫ p, h p ∂(PX.prod PY) := by
    intro h hm
    rw [← hjoint, integral_map hUV.aemeasurable hm.aestronglyMeasurable]
  simp_rw [hfω, hgω]
  rw [hE (fun p => F p * G p) (hFm.mul hGm), hE F hFm, hE G hGm]
  have hFGi : Integrable (fun p => F p * G p) (PX.prod PY) :=
    bdd_integrable _ _ (hFm.mul hGm) (Cf * Cg) (fun p => by
      rw [abs_mul]; exact mul_le_mul (hFb p) (hGb p) (abs_nonneg _)
        (le_trans (abs_nonneg _) (hFb p)))
  have hFi : Integrable F (PX.prod PY) := bdd_integrable _ _ hFm Cf hFb
  have hGi : Integrable G (PX.prod PY) := bdd_integrable _ _ hGm Cg hGb
  rw [integral_prod_symm _ hFGi, integral_prod_symm _ hFi, integral_prod_symm _ hGi]
  -- index sets on each side
  let A1 : Finset κ₁ := Finset.univ.filter (fun i => Sum.inl i ∈ A)
  let B1 : Finset κ₁ := Finset.univ.filter (fun i => Sum.inl i ∈ B)
  let A2 : Finset κ₂ := Finset.univ.filter (fun j => Sum.inr j ∈ A)
  let B2 : Finset κ₂ := Finset.univ.filter (fun j => Sum.inr j ∈ B)
  have hA1B1 : Disjoint A1 B1 := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [A1, B1, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact Finset.disjoint_left.mp hAB h1 h2
  have hA2B2 : Disjoint A2 B2 := by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [A2, B2, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact Finset.disjoint_left.mp hAB h1 h2
  -- inner step: for fixed `v`, NA of `X`
  let φ : (κ₂ → ℝ) → ℝ := fun v => ∫ u, F (u, v) ∂PX
  let ψ : (κ₂ → ℝ) → ℝ := fun v => ∫ u, G (u, v) ∂PX
  have hinner : ∀ v, ∫ u, F (u, v) * G (u, v) ∂PX ≤ φ v * ψ v := by
    intro v
    let f1 : (A1 → ℝ) → ℝ := fun z => f (fun a : A => Sum.elim (ext0 A1 z) v a.1)
    let g1 : (B1 → ℝ) → ℝ := fun z => g (fun b : B => Sum.elim (ext0 B1 z) v b.1)
    have hF1 : ∀ u, F (u, v) = f1 (fun a : A1 => u a) := by
      intro u
      simp only [F, f1]
      congr 1; funext a
      rcases a with ⟨a | a, ha⟩
      · simp only [Sum.elim_inl]
        rw [ext0_restrict A1 u a (by simp [A1, ha])]
      · rfl
    have hG1 : ∀ u, G (u, v) = g1 (fun b : B1 => u b) := by
      intro u
      simp only [G, g1]
      congr 1; funext b
      rcases b with ⟨b | b, hb⟩
      · simp only [Sum.elim_inl]
        rw [ext0_restrict B1 u b (by simp [B1, hb])]
      · rfl
    have hf1 : Monotone f1 := by
      intro z z' h; apply hf; intro a
      rcases a with ⟨a | a, _⟩
      · exact ext0_mono A1 h a
      · exact le_rfl
    have hg1 : Monotone g1 := by
      intro z z' h; apply hg; intro b
      rcases b with ⟨b | b, _⟩
      · exact ext0_mono B1 h b
      · exact le_rfl
    have hf1m : Measurable f1 := by
      apply hfm.comp
      apply measurable_pi_lambda
      intro a
      rcases a with ⟨a | a, _⟩
      · exact (measurable_pi_apply a).comp (ext0_meas A1)
      · exact measurable_const
    have hg1m : Measurable g1 := by
      apply hgm.comp
      apply measurable_pi_lambda
      intro b
      rcases b with ⟨b | b, _⟩
      · exact (measurable_pi_apply b).comp (ext0_meas B1)
      · exact measurable_const
    have := NA_law μ X hX hXNA A1 B1 hA1B1 f1 g1 hf1 hg1 hf1m hg1m ⟨Cf, fun y => hCf _⟩
      ⟨Cg, fun y => hCg _⟩
    simp only [φ, ψ, hF1, hG1]
    exact this
  -- outer step: NA of `Y`
  let f2 : (A2 → ℝ) → ℝ := fun z => ∫ u, f (fun a : A => Sum.elim u (ext0 A2 z) a.1) ∂PX
  let g2 : (B2 → ℝ) → ℝ := fun z => ∫ u, g (fun b : B => Sum.elim u (ext0 B2 z) b.1) ∂PX
  have hφ : ∀ v, φ v = f2 (fun a : A2 => v a) := by
    intro v
    simp only [φ, f2, F]
    congr 1; funext u; congr 1; funext a
    rcases a with ⟨a | a, ha⟩
    · rfl
    · simp only [Sum.elim_inr]
      rw [ext0_restrict A2 v a (by simp [A2, ha])]
  have hψ : ∀ v, ψ v = g2 (fun b : B2 => v b) := by
    intro v
    simp only [ψ, g2, G]
    congr 1; funext u; congr 1; funext b
    rcases b with ⟨b | b, hb⟩
    · rfl
    · simp only [Sum.elim_inr]
      rw [ext0_restrict B2 v b (by simp [B2, hb])]
  have hjm_f : ∀ (S : Finset κ₂), Measurable (fun p : (κ₁ → ℝ) × (S → ℝ) =>
      f (fun a : A => Sum.elim p.1 (ext0 S p.2) a.1)) := by
    intro S
    apply hfm.comp
    apply measurable_pi_lambda
    intro a
    rcases a with ⟨a | a, _⟩
    · exact (measurable_pi_apply a).comp measurable_fst
    · exact (measurable_pi_apply a).comp ((ext0_meas S).comp measurable_snd)
  have hjm_g : ∀ (S : Finset κ₂), Measurable (fun p : (κ₁ → ℝ) × (S → ℝ) =>
      g (fun b : B => Sum.elim p.1 (ext0 S p.2) b.1)) := by
    intro S
    apply hgm.comp
    apply measurable_pi_lambda
    intro b
    rcases b with ⟨b | b, _⟩
    · exact (measurable_pi_apply b).comp measurable_fst
    · exact (measurable_pi_apply b).comp ((ext0_meas S).comp measurable_snd)
  have hf2m : Measurable f2 :=
    (StronglyMeasurable.integral_prod_left' (μ := PX) (hjm_f A2).stronglyMeasurable).measurable
  have hg2m : Measurable g2 :=
    (StronglyMeasurable.integral_prod_left' (μ := PX) (hjm_g B2).stronglyMeasurable).measurable
  have hf2 : Monotone f2 := by
    intro z z' h
    apply integral_mono
    · exact bdd_integrable _ _ ((hjm_f A2).comp (measurable_id.prodMk measurable_const)) Cf
        (fun u => hCf _)
    · exact bdd_integrable _ _ ((hjm_f A2).comp (measurable_id.prodMk measurable_const)) Cf
        (fun u => hCf _)
    · intro u; apply hf; intro a
      rcases a with ⟨a | a, _⟩
      · exact le_rfl
      · exact ext0_mono A2 h a
  have hg2 : Monotone g2 := by
    intro z z' h
    apply integral_mono
    · exact bdd_integrable _ _ ((hjm_g B2).comp (measurable_id.prodMk measurable_const)) Cg
        (fun u => hCg _)
    · exact bdd_integrable _ _ ((hjm_g B2).comp (measurable_id.prodMk measurable_const)) Cg
        (fun u => hCg _)
    · intro u; apply hg; intro b
      rcases b with ⟨b | b, _⟩
      · exact le_rfl
      · exact ext0_mono B2 h b
  have hf2b : ∃ C : ℝ, ∀ y, |f2 y| ≤ C := ⟨Cf, fun y => abs_integral_le PX _ Cf (fun u => hCf _)⟩
  have hg2b : ∃ C : ℝ, ∀ y, |g2 y| ≤ C := ⟨Cg, fun y => abs_integral_le PX _ Cg (fun u => hCg _)⟩
  have hout := NA_law μ Y hY hYNA A2 B2 hA2B2 f2 g2 hf2 hg2 hf2m hg2m hf2b hg2b
  -- assemble
  have hφm : Measurable φ :=
    (StronglyMeasurable.integral_prod_left' (μ := PX) hFm.stronglyMeasurable).measurable
  have hψm : Measurable ψ :=
    (StronglyMeasurable.integral_prod_left' (μ := PX) hGm.stronglyMeasurable).measurable
  have hFGm : Measurable (fun v => ∫ u, F (u, v) * G (u, v) ∂PX) :=
    (StronglyMeasurable.integral_prod_left' (μ := PX)
      (hFm.mul hGm).stronglyMeasurable).measurable
  calc ∫ v, ∫ u, F (u, v) * G (u, v) ∂PX ∂PY
      ≤ ∫ v, φ v * ψ v ∂PY := by
        apply integral_mono
        · exact bdd_integrable _ _ hFGm (Cf * Cg) (fun v => abs_integral_le PX _ _ (fun u => by
            rw [abs_mul]; exact mul_le_mul (hFb _) (hGb _) (abs_nonneg _)
              (le_trans (abs_nonneg _) (hFb (u, v)))))
        · exact bdd_integrable _ _ (hφm.mul hψm) (Cf * Cg) (fun v => by
            rw [abs_mul]
            exact mul_le_mul (abs_integral_le PX _ Cf (fun u => hFb _))
              (abs_integral_le PX _ Cg (fun u => hGb _)) (abs_nonneg _)
              (le_trans (abs_nonneg _) (abs_integral_le PX _ Cf (fun u => hFb (u, v)))))
        · exact hinner
    _ = ∫ v, f2 (fun a : A2 => v a) * g2 (fun b : B2 => v b) ∂PY := by
        congr 1; funext v; rw [hφ, hψ]
    _ ≤ (∫ v, f2 (fun a : A2 => v a) ∂PY) * ∫ v, g2 (fun b : B2 => v b) ∂PY := hout
    _ = (∫ v, φ v ∂PY) * ∫ v, ψ v ∂PY := by
        congr 1
        · congr 1; funext v; rw [hφ]
        · congr 1; funext v; rw [hψ]
