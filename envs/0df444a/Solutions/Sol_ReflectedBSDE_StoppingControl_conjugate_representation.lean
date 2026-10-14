-- Prove2me | solution 1 for ReflectedBSDE.StoppingControl.conjugate_representation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T01:38:36.381093+00:00
-- url     : https://prove2.me/submissions/251d3bdd-9993-4f3d-9f2f-1f365c8e9c71

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MultiperiodRisk_Bellman_EssInf
import Definitions.Def_ReflectedBSDE_StoppingControl_Setting
import Definitions.Def_ReflectedBSDE_StoppingControl_Control



namespace ReflectedBSDE.StoppingControl

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

lemma cr_supergrad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (g : E → ℝ) (hg : ConcaveOn ℝ Set.univ g) (x0 : E) :
    ∃ ℓ : E →L[ℝ] ℝ, ∀ x, g x ≤ g x0 + ℓ (x - x0) := by
  have hc : Continuous g := hg.locallyLipschitz.continuous
  let A : Set (E × ℝ) := {q | q.2 < g q.1}
  have hA_open : IsOpen A := isOpen_lt continuous_snd (hc.comp continuous_fst)
  have hA_conv : Convex ℝ A := by
    intro q hq q' hq' a b ha hb hab
    have h1 : q.2 < g q.1 := hq
    have h2 : q'.2 < g q'.1 := hq'
    have := hg.2 (Set.mem_univ q.1) (Set.mem_univ q'.1) ha hb hab
    show (a • q + b • q').2 < g (a • q + b • q').1
    simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_add, Prod.smul_fst, smul_eq_mul] at this ⊢
    rcases ha.lt_or_eq with ha' | ha'
    · have : a * q.2 < a * g q.1 := mul_lt_mul_of_pos_left h1 ha'
      have : b * q'.2 ≤ b * g q'.1 := mul_le_mul_of_nonneg_left h2.le hb
      linarith
    · subst ha'
      have hb1 : b = 1 := by linarith
      subst hb1
      simp only [zero_mul, zero_add, one_mul, zero_smul, one_smul] at this ⊢
      linarith
  have hnot : (x0, g x0) ∉ A := fun h => lt_irrefl _ (show g x0 < g x0 from h)
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hA_conv hA_open hnot
  set c := φ ((0 : E), (1 : ℝ)) with hcdef
  have hsplit : ∀ (x : E) (s : ℝ), φ (x, s) = φ (x, 0) + s * c := by
    intro x s
    have : ((x, s) : E × ℝ) = (x, 0) + s • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hcpos : 0 < c := by
    have := hφ (x0, g x0 - 1) (show g x0 - 1 < g x0 by linarith)
    rw [hsplit x0 (g x0 - 1), hsplit x0 (g x0)] at this
    linarith
  have key : ∀ x, φ (x, 0) + g x * c ≤ φ (x0, 0) + g x0 * c := by
    intro x
    by_contra hcon
    push Not at hcon
    set ε := (φ (x, 0) + g x * c - (φ (x0, 0) + g x0 * c)) / c with hε
    have hεpos : 0 < ε := div_pos (by linarith) hcpos
    have hεc : ε * c = φ (x, 0) + g x * c - (φ (x0, 0) + g x0 * c) := by
      rw [hε]; field_simp
    have := hφ (x, g x - ε) (show g x - ε < g x by linarith)
    rw [hsplit x (g x - ε), hsplit x0 (g x0)] at this
    nlinarith
  refine ⟨(-(1 / c)) • (φ.comp (ContinuousLinearMap.inl ℝ E ℝ)), fun x => ?_⟩
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, smul_eq_mul, map_sub]
  have hk := key x
  have : g x - g x0 ≤ (φ (x0, 0) - φ (x, 0)) / c := by
    rw [le_div_iff₀ hcpos]; linarith
  have h2 : -(1 / c) * φ (x, 0) - -(1 / c) * φ (x0, 0) = (φ (x0, 0) - φ (x, 0)) / c := by
    field_simp; ring
  linarith

lemma cr_linrepr {d : ℕ} (ℓ : (ℝ × (Fin d → ℝ)) →L[ℝ] ℝ) (y : ℝ) (z : Fin d → ℝ) :
    ℓ (y, z) = ℓ (1, 0) * y + dot (fun j => ℓ (0, fun k => if j = k then 1 else 0)) z := by
  have h1 : ((y, z) : ℝ × (Fin d → ℝ)) = y • ((1 : ℝ), (0 : Fin d → ℝ)) + ((0 : ℝ), z) := by
    ext <;> simp
  rw [h1, map_add, map_smul, smul_eq_mul]
  have h2 : ℓ ((0 : ℝ), z) = (ℓ.comp (ContinuousLinearMap.inr ℝ ℝ (Fin d → ℝ))).toLinearMap z := by
    simp
  rw [h2, LinearMap.pi_apply_eq_sum_univ]
  unfold dot
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply, smul_eq_mul]
  congr 1
  · ring
  · exact Finset.sum_congr rfl (fun j _ => by ring)

lemma cr_toReal_ge (e : EReal) (r : ℝ) (h : (r : EReal) ≤ e) (hlt : e < ⊤) : r ≤ e.toReal := by
  have hb : e ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot r) h
  rw [← EReal.coe_toReal hlt.ne hb] at h
  exact EReal.coe_le_coe_iff.1 h

lemma cr_term_le {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (ω : Ω) (t : ℝ≥0) (β : ℝ) (γ : Fin d → ℝ) (y : ℝ) (z : Fin d → ℝ) :
    ((f t ω y z - β * y - dot γ z : ℝ) : EReal) ≤ conj f ω t β γ := by
  unfold conj
  exact le_iSup₂_of_le (f := fun (y : ℝ) (z : Fin d → ℝ) =>
    ((f t ω y z - β * y - dot γ z : ℝ) : EReal)) y z le_rfl

lemma cr_aux (a K C : ℝ) (hK : 0 < K) (h : ∀ c : ℝ, 0 ≤ c → c * (a ^ 2 - K * a) ≤ C) :
    a ≤ K := by
  by_contra hcon
  push Not at hcon
  have hD : 0 < a ^ 2 - K * a := by nlinarith
  have := h ((|C| + 1) / (a ^ 2 - K * a)) (div_nonneg (by positivity) hD.le)
  rw [div_mul_cancel₀ _ hD.ne'] at this
  have := le_abs_self C
  linarith

lemma cr_eucNorm_smul {d : ℕ} (c : ℝ) (hc : 0 ≤ c) (p : Fin d → ℝ) :
    eucNorm ((fun j => -c * p j) - 0) = c * eucNorm p := by
  unfold eucNorm
  have : (∑ j, ((fun j => -c * p j) - (0 : Fin d → ℝ)) j ^ 2) = c ^ 2 * ∑ j, p j ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by simp; ring)
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

lemma cr_eucNorm_zero {d : ℕ} : eucNorm ((0 : Fin d → ℝ) - 0) = 0 := by
  simp [eucNorm]

lemma cr_eucNorm_sq {d : ℕ} (p : Fin d → ℝ) : eucNorm p ^ 2 = ∑ j, p j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem conjugate_representation_core {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (hLip : ∃ K : ℝ, IsLipschitzCoeff P T f K) :
    (∀ ω, ∀ t ≤ T, ∀ (y : ℝ) (z : Fin d → ℝ),
      (∀ p ∈ conjDomain f ω t, f t ω y z ≤ (conj f ω t p.1 p.2).toReal + p.1 * y + dot p.2 z) ∧
      ∃ p ∈ conjDomain f ω t, f t ω y z = (conj f ω t p.1 p.2).toReal + p.1 * y + dot p.2 z) ∧
    ∀ᵐ ω ∂P, ∀ t ≤ T, Bornology.IsBounded (conjDomain f ω t) := by
  refine ⟨fun ω t ht y z => ⟨fun p hp => ?_, ?_⟩, ?_⟩
  · have := cr_toReal_ge _ _ (cr_term_le f ω t p.1 p.2 y z) hp
    linarith
  · obtain ⟨ℓ, hℓ⟩ := cr_supergrad _ (hconc ω t ht) (y, z)
    set β := ℓ (1, 0)
    set γ : Fin d → ℝ := fun j => ℓ (0, fun k => if j = k then 1 else 0)
    have hle : ∀ y' z', f t ω y' z' - β * y' - dot γ z' ≤ f t ω y z - β * y - dot γ z := by
      intro y' z'
      have h := hℓ (y', z')
      simp only at h
      rw [map_sub, cr_linrepr ℓ y' z', cr_linrepr ℓ y z] at h
      linarith
    have hconj : conj f ω t β γ = ((f t ω y z - β * y - dot γ z : ℝ) : EReal) := by
      apply le_antisymm
      · unfold conj
        exact iSup₂_le fun y' z' => EReal.coe_le_coe_iff.2 (hle y' z')
      · exact cr_term_le f ω t β γ y z
    refine ⟨(β, γ), ?_, ?_⟩
    · show conj f ω t β γ < ⊤
      rw [hconj]; exact EReal.coe_lt_top _
    · show f t ω y z = (conj f ω t β γ).toReal + β * y + dot γ z
      rw [hconj, EReal.toReal_coe]; ring
  · obtain ⟨K, hK, hae⟩ := hLip
    filter_upwards [hae] with ω hω t ht
    refine (Metric.isBounded_closedBall (x := (0 : ℝ × (Fin d → ℝ))) (r := K)).subset ?_
    intro p hp
    have hp' : conj f ω t p.1 p.2 < ⊤ := hp
    set M := (conj f ω t p.1 p.2).toReal
    have hM : ∀ y z, f t ω y z - p.1 * y - dot p.2 z ≤ M := fun y z =>
      cr_toReal_ge _ _ (cr_term_le f ω t p.1 p.2 y z) hp'
    have hb1 : |p.1| ≤ K := by
      apply cr_aux _ K (M - f t ω 0 0) hK
      intro c hc
      have h1 := hM (-c * p.1) 0
      have h2 := hω t ht (-c * p.1) 0 0 0
      rw [cr_eucNorm_zero] at h2
      have hd : dot p.2 (0 : Fin d → ℝ) = 0 := by simp [dot]
      rw [hd] at h1
      have habs : |-c * p.1 - 0| = c * |p.1| := by
        rw [sub_zero, abs_mul, abs_neg, abs_of_nonneg hc]
      rw [habs] at h2
      have h3 := neg_abs_le (f t ω (-c * p.1) 0 - f t ω 0 0)
      have h4 : p.1 ^ 2 = |p.1| ^ 2 := (sq_abs _).symm
      nlinarith
    have hb2 : eucNorm p.2 ≤ K := by
      apply cr_aux _ K (M - f t ω 0 0) hK
      intro c hc
      have h1 := hM 0 (fun j => -c * p.2 j)
      have h2 := hω t ht 0 0 (fun j => -c * p.2 j) 0
      rw [cr_eucNorm_smul c hc] at h2
      have hd : dot p.2 (fun j => -c * p.2 j) = -c * eucNorm p.2 ^ 2 := by
        rw [cr_eucNorm_sq]; unfold dot; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      rw [hd] at h1
      have h3 := neg_abs_le (f t ω 0 (fun j => -c * p.2 j) - f t ω 0 0)
      simp only [sub_zero, abs_zero, zero_add, mul_zero] at h1 h2
      nlinarith
    rw [Metric.mem_closedBall, dist_zero_right, norm_prod_le_iff]
    refine ⟨by simpa [Real.norm_eq_abs] using hb1, ?_⟩
    rw [pi_norm_le_iff_of_nonneg hK.le]
    intro j
    rw [Real.norm_eq_abs]
    refine le_trans ?_ hb2
    unfold eucNorm
    apply Real.abs_le_sqrt
    exact Finset.single_le_sum (f := fun i => p.2 i ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)

end ReflectedBSDE.StoppingControl

open ReflectedBSDE.StoppingControl
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (T : ℝ≥0) (f : ℝ≥0 → Ω → ℝ → (Fin d → ℝ) → ℝ)
    (hconc : ∀ ω, ∀ t ≤ T, ConcaveOn ℝ Set.univ (fun p : ℝ × (Fin d → ℝ) => f t ω p.1 p.2))
    (hLip : ∃ K : ℝ, IsLipschitzCoeff P T f K) :
    (∀ ω, ∀ t ≤ T, ∀ (y : ℝ) (z : Fin d → ℝ),
      (∀ p ∈ conjDomain f ω t, f t ω y z ≤ (conj f ω t p.1 p.2).toReal + p.1 * y + dot p.2 z) ∧
      ∃ p ∈ conjDomain f ω t, f t ω y z = (conj f ω t p.1 p.2).toReal + p.1 * y + dot p.2 z) ∧
    ∀ᵐ ω ∂P, ∀ t ≤ T, Bornology.IsBounded (conjDomain f ω t) := by
  exact conjugate_representation_core P T f hconc hLip
