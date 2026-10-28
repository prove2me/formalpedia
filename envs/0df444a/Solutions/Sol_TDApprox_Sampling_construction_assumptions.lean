-- Prove2me | solution 1 for TDApprox.Sampling.construction_assumptions
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T23:46:00.980628+00:00
-- url     : https://prove2.me/submissions/2305b643-bcc6-4eda-bbcf-ddb7e28d6ef6

import Mathlib
import Definitions.Def_TDApprox_Sampling_Model

open MeasureTheory ProbabilityTheory

namespace Aux_TDApprox_Sampling_construction_assumptions

open TDApprox.Sampling

lemma law_one {S : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (p : Measure S) [IsProbabilityMeasure p] (i : S) :
    (pathLaw (rowKernel p) i).map (fun ω => ω 1) = p := by
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => S) (μ₀ := Measure.dirac i)
    (κ := fun n => (rowKernel p).comap
      (fun x : (k : Finset.Iic n) → S => x ⟨n, Finset.mem_Iic.mpr (le_refl n)⟩) (by fun_prop))
    (a := 0)
  have h2 := congrArg (fun μ => Measure.map Prod.snd μ) h
  unfold pathLaw
  set T := Kernel.trajMeasure (X := fun _ => S) (Measure.dirac i) (fun n => (rowKernel p).comap
      (fun x : (k : Finset.Iic n) → S => x ⟨n, Finset.mem_Iic.mpr (le_refl n)⟩) (by fun_prop))
    with hT
  have e1 : Measure.map Prod.snd (Measure.map (fun x : ℕ → S =>
      (Preorder.frestrictLe 0 x, x (0 + 1))) T) = Measure.map (fun ω : ℕ → S => ω 1) T := by
    rw [Measure.map_map measurable_snd (by fun_prop)]
    rfl
  have e2 : Measure.map Prod.snd (Measure.map (Preorder.frestrictLe 0) T ⊗ₘ
      (rowKernel p).comap (fun x : (k : Finset.Iic 0) → S => x ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
        (by fun_prop)) = p := by
    change (Measure.map (Preorder.frestrictLe 0) T ⊗ₘ _).snd = p
    rw [Measure.snd_compProd]
    ext s hs
    rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
    haveI : IsProbabilityMeasure (Measure.map (Preorder.frestrictLe 0) T) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    simp [rowKernel, Kernel.comap_apply]
  calc Measure.map (fun ω : ℕ → S => ω 1) T
      = Measure.map Prod.snd (Measure.map (fun x : ℕ → S =>
          (Preorder.frestrictLe 0 x, x (0 + 1))) T) := e1.symm
    _ = _ := h2.symm
    _ = p := e2

lemma tsum_two {S : Type*} (s₁ s₂ : S) (hne : s₁ ≠ s₂) (f : S → ℝ)
    (h : ∀ i, i ≠ s₁ → i ≠ s₂ → f i = 0) : ∑' i, f i = f s₁ + f s₂ := by
  classical
  rw [tsum_eq_sum (s := {s₁, s₂}) (fun b hb => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
    exact h b hb.1 hb.2), Finset.sum_pair hne]

end Aux_TDApprox_Sampling_construction_assumptions

open Aux_TDApprox_Sampling_construction_assumptions in
open TDApprox.Sampling in
theorem solution
    {S : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    (s₁ s₂ : S) (hne : s₁ ≠ s₂) (α : ℝ) (hα₁ : (5 : ℝ) / 6 < α)
    (hα₂ : α < 1) (p : Measure S) [IsProbabilityMeasure p]
    (hp : ∀ i, 0 < p {i})
    (hp₂ : 5 / (6 * α) < (p {s₂}).toReal)
    (hp₂lt : (p {s₂}).toReal < 1) :
    let P := rowKernel p
    let φ := sampleFeature s₁ s₂
    Assumption1 P p (fun _ _ => 0) α ∧
      Assumption2 p φ ∧
      TDApprox.Conv.Jstar P (fun _ _ => 0) α = (fun _ => 0) ∧
      (∀ r : Fin 1 → ℝ,
        proj p φ (T0 P (fun _ _ => 0) α (fun i => dotProduct (φ i) r)) =
          (fun i => dotProduct (φ i) r) ↔ r = 0) := by
  intro P φ
  have hφ1 : ∀ k, φ s₁ k = 1 := by
    intro k; simp [φ, sampleFeature]
  have hφ2 : ∀ k, φ s₂ k = 2 := by
    intro k; simp [φ, sampleFeature, Ne.symm hne]
  have hφ0 : ∀ i k, i ≠ s₁ → i ≠ s₂ → φ i k = 0 := by
    intro i k h1 h2; simp [φ, sampleFeature, h1, h2]
  have hφb : ∀ i k, |φ i k| ≤ 2 := by
    intro i k
    by_cases h1 : i = s₁
    · subst h1; rw [hφ1]; norm_num
    by_cases h2 : i = s₂
    · subst h2; rw [hφ2]; norm_num
    rw [hφ0 i k h1 h2]; norm_num
  have hP : ∀ x, P x = p := fun x => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, hp, ?_, ?_⟩
    · show p.bind P = p
      ext s hs
      rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
      simp [hP]
    · intro ν _ hν
      have hν' : ν.bind P = ν := hν
      ext s hs
      rw [← hν', Measure.bind_apply hs (Kernel.aemeasurable _)]
      simp [hP]
    · simp
    · intro i
      simp
  · refine ⟨?_, ?_⟩
    · rw [linearIndependent_unique_iff]
      intro h0
      have := congrFun h0 s₁
      simp only [Pi.zero_apply] at this
      rw [hφ1] at this
      exact one_ne_zero this
    · intro k
      refine Integrable.of_bound (Measurable.of_discrete).aestronglyMeasurable 4
        (Filter.Eventually.of_forall (fun i => ?_))
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have := hφb i k
      have h2 : φ i k ^ 2 = |φ i k| ^ 2 := (sq_abs _).symm
      nlinarith [abs_nonneg (φ i k)]
  · funext i
    simp [TDApprox.Conv.Jstar]
  · intro r
    set p1 := (p {s₁}).toReal with hp1
    set p2 := (p {s₂}).toReal with hp2
    have hp1pos : 0 < p1 := ENNReal.toReal_pos (hp s₁).ne' (measure_ne_top _ _)
    have hp2pos : 0 < p2 := ENNReal.toReal_pos (hp s₂).ne' (measure_ne_top _ _)
    have hsum12 : p1 + p2 ≤ 1 := by
      have h := measure_union (μ := p) (Set.disjoint_singleton.2 hne) (measurableSet_singleton s₂)
      have hle : p ({s₁} ∪ {s₂}) ≤ 1 := prob_le_one
      rw [h] at hle
      have := ENNReal.toReal_mono ENNReal.one_ne_top hle
      rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at this
      exact this
    set c := p1 + 2 * p2 with hc
    set G := p1 + 4 * p2 with hG
    have hGpos : 0 < G := by positivity
    have hcG : c ^ 2 ≤ G := by
      rw [hc, hG]; nlinarith
    -- integral against p
    have hint_p : ∀ (f : S → ℝ), (∀ i, i ≠ s₁ → i ≠ s₂ → f i = 0) → (∀ i, |f i| ≤ |f s₁| + |f s₂|) →
        ∫ s, f s ∂p = p1 * f s₁ + p2 * f s₂ := by
      intro f hf hfb
      have hI : Integrable f p := Integrable.of_bound (Measurable.of_discrete).aestronglyMeasurable
        (|f s₁| + |f s₂|) (Filter.Eventually.of_forall (fun i => by
          rw [Real.norm_eq_abs]; exact hfb i))
      rw [integral_countable hI, tsum_two s₁ s₂ hne _ (fun i h1 h2 => by rw [hf i h1 h2, smul_zero])]
      simp only [smul_eq_mul, Measure.real, hp1, hp2]
    -- T0 is constant
    have hT0 : ∀ i, T0 P (fun _ _ => 0) α (fun i => dotProduct (φ i) r) i = α * (r 0 * c) := by
      intro i
      unfold T0
      simp only [zero_add]
      rw [integral_const_mul]
      congr 1
      have hmap := law_one p i
      have hmeas : Measurable (fun ω : ℕ → S => ω 1) := measurable_pi_apply 1
      rw [← integral_map (f := fun s => dotProduct (φ s) r) (φ := fun ω : ℕ → S => ω 1)
        hmeas.aemeasurable (Measurable.of_discrete).aestronglyMeasurable]
      rw [(hmap : Measure.map (fun ω : ℕ → S => ω 1) (pathLaw P i) = p)]
      rw [hint_p (fun i => dotProduct (φ i) r)]
      · simp only [dotProduct, Fin.sum_univ_one, hφ1, hφ2, hc]; ring
      · intro j h1 h2; simp only [dotProduct, Fin.sum_univ_one, hφ0 j 0 h1 h2, zero_mul]
      · intro j
        simp only [dotProduct, Fin.sum_univ_one, hφ1, hφ2]
        by_cases h1 : j = s₁
        · subst h1; rw [hφ1]; have := abs_nonneg (2 * r 0); linarith
        by_cases h2 : j = s₂
        · subst h2; rw [hφ2]; have := abs_nonneg (1 * r 0); linarith
        rw [hφ0 j 0 h1 h2, zero_mul, abs_zero]; positivity
    -- gram and feature moment
    have hgram : gram p φ 0 0 = G := by
      unfold gram
      rw [tsum_two s₁ s₂ hne _ (fun i h1 h2 => by rw [hφ0 i 0 h1 h2]; ring), hφ1, hφ2, hG]
      ring
    have hfm : ∀ C : ℝ, featureMoment p φ (fun _ => C) 0 = C * c := by
      intro C
      unfold featureMoment
      rw [tsum_two s₁ s₂ hne _ (fun i h1 h2 => by rw [hφ0 i 0 h1 h2]; ring), hφ1, hφ2, hc]
      ring
    have hinv : (gram p φ)⁻¹ 0 0 = 1 / G := by
      have hdet : IsUnit (gram p φ).det := by
        rw [Matrix.det_unique, isUnit_iff_ne_zero]
        show gram p φ 0 0 ≠ 0
        rw [hgram]; exact hGpos.ne'
      have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv (gram p φ) hdet) 0) 0
      rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.one_apply_eq, hgram] at h1
      field_simp
      linarith
    have hproj : ∀ i, proj p φ (T0 P (fun _ _ => 0) α (fun i => dotProduct (φ i) r)) i =
        φ i 0 * (1 / G * (α * (r 0 * c) * c)) := by
      intro i
      have hT0f : T0 P (fun _ _ => 0) α (fun i => dotProduct (φ i) r) =
          fun _ => α * (r 0 * c) := funext hT0
      unfold proj
      rw [hT0f]
      simp only [dotProduct, Fin.sum_univ_one, Matrix.mulVec, hinv, hfm]
    constructor
    · intro hfix
      have h1 := congrFun hfix s₁
      rw [hproj] at h1
      simp only [dotProduct, Fin.sum_univ_one, hφ1, one_mul] at h1
      have hα0 : 0 < α := by linarith
      have hkey : r 0 * (α * c ^ 2 - G) = 0 := by
        field_simp at h1
        linarith
      have hne0 : α * c ^ 2 - G ≠ 0 := by
        have : α * c ^ 2 < G := by
          calc α * c ^ 2 ≤ α * G := mul_le_mul_of_nonneg_left hcG hα0.le
            _ < 1 * G := mul_lt_mul_of_pos_right hα₂ hGpos
            _ = G := one_mul G
        linarith
      have hr0 : r 0 = 0 := (mul_eq_zero.1 hkey).resolve_right hne0
      funext k
      fin_cases k
      simpa using hr0
    · intro hr
      funext i
      rw [hproj]
      simp [hr, dotProduct]
