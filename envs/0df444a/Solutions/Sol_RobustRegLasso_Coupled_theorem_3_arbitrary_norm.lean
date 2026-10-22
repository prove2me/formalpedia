-- Prove2me | solution 1 for RobustRegLasso.Coupled.theorem_3_arbitrary_norm
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:49:40.988155+00:00
-- url     : https://prove2.me/submissions/05f00656-46eb-42b0-a98c-29ae5425707d

import Mathlib
import Definitions.Def_RobustRegLasso_Coupled_Basic

set_option autoImplicit false
open RobustRegLasso.Coupled

theorem rrc_matVec_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (a δ : Fin m → E) (x : Fin m → ℝ) : matVec (a + δ) x = matVec a x + matVec δ x := by
  simp [matVec, smul_add, Finset.sum_add_distrib]

theorem rrc_greatest {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {m : ℕ} (a : Fin m → E) (b : E) (c : Fin m → ℝ) (hc0 : ∀ i, 0 ≤ c i)
    (x : Fin m → ℝ) :
    IsGreatest (residualValues a b (uncertaintySetA c) x)
        (‖b - matVec a x‖ + ∑ i, c i * |x i|) := by
  set r : E := b - matVec a x with hr
  have hres : ∀ δ : Fin m → E, perturbedResidual a δ b x = ‖r - matVec δ x‖ := by
    intro δ
    simp only [perturbedResidual, rrc_matVec_add, hr]
    congr 1; abel
  refine ⟨?_, ?_⟩
  · obtain ⟨u, hu1, hru⟩ : ∃ u : E, ‖u‖ = 1 ∧ r = ‖r‖ • u := by
      by_cases h0 : r = 0
      · obtain ⟨v, hv⟩ := exists_ne (0 : E)
        refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
        · rw [norm_smul, norm_inv, norm_norm]
          exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
        · rw [h0]; simp
      · have hn : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr h0
        refine ⟨‖r‖⁻¹ • r, ?_, ?_⟩
        · rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ hn
        · rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    set sg : Fin m → ℝ := fun i => if x i < 0 then -1 else 1 with hsg
    set δ : Fin m → E := fun i => (-(c i * sg i)) • u with hδ
    have hsg1 : ∀ i, |sg i| = 1 := fun i => by
      simp only [hsg]; split_ifs <;> simp
    have hxsg : ∀ i, x i * sg i = |x i| := fun i => by
      simp only [hsg]
      split_ifs with h
      · rw [abs_of_neg h]; ring
      · rw [abs_of_nonneg (not_lt.mp h)]; ring
    have hnorm : ∀ i, ‖δ i‖ = c i := fun i => by
      simp only [hδ, norm_smul, hu1, mul_one, Real.norm_eq_abs, abs_neg, abs_mul, hsg1,
        abs_of_nonneg (hc0 i)]
    have hδU : δ ∈ uncertaintySetA c := fun i => (hnorm i).le
    have hmv : matVec δ x = (-(∑ i, c i * |x i|)) • u := by
      simp only [matVec, hδ, smul_smul]
      rw [← Finset.sum_smul, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hxsg i]; ring
    have hS : 0 ≤ ∑ i, c i * |x i| := Finset.sum_nonneg fun i _ => mul_nonneg (hc0 i) (abs_nonneg _)
    refine ⟨δ, hδU, ?_⟩
    show perturbedResidual a δ b x = _
    rw [hres, hmv]
    have : r - (-(∑ i, c i * |x i|)) • u = (‖r‖ + ∑ i, c i * |x i|) • u := by
      conv_lhs => rw [hru]
      rw [neg_smul, sub_neg_eq_add, ← add_smul]
    rw [this, norm_smul, hu1, mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  · rintro _ ⟨δ, hδ, rfl⟩
    show perturbedResidual a δ b x ≤ _
    rw [hres]
    calc ‖r - matVec δ x‖ ≤ ‖r‖ + ‖matVec δ x‖ := norm_sub_le _ _
      _ ≤ ‖r‖ + ∑ i, c i * |x i| := by
        refine add_le_add (le_refl _) ?_
        refine (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hδ i) (abs_nonneg _)

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {m : ℕ} (a : Fin m → E) (b : E) (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (∀ x : Fin m → ℝ,
      IsGreatest (residualValues a b (uncertaintySetA c) x)
        (‖b - matVec a x‖ + ∑ i, c i * |x i|)) ∧
    {x : Fin m → ℝ | ∀ x' : Fin m → ℝ,
        robustObjective a b (uncertaintySetA c) x ≤ robustObjective a b (uncertaintySetA c) x'} =
      {x : Fin m → ℝ | ∀ x' : Fin m → ℝ,
        ‖b - matVec a x‖ + ∑ i, c i * |x i| ≤ ‖b - matVec a x'‖ + ∑ i, c i * |x' i|} := by
  have hG := rrc_greatest a b c hc
  refine ⟨hG, ?_⟩
  have hobj : ∀ x, robustObjective a b (uncertaintySetA c) x =
      ((‖b - matVec a x‖ + ∑ i, c i * |x i| : ℝ) : EReal) := by
    intro x
    obtain ⟨⟨δ, hδ, hδv⟩, hub⟩ := hG x
    apply le_antisymm
    · refine iSup₂_le fun δ' hδ' => ?_
      exact EReal.coe_le_coe_iff.mpr (hub ⟨δ', hδ', rfl⟩)
    · rw [← hδv]
      exact le_iSup₂ (f := fun δ (_ : δ ∈ uncertaintySetA c) =>
        ((perturbedResidual a δ b x : ℝ) : EReal)) δ hδ
  ext x
  simp only [Set.mem_setOf_eq, hobj, EReal.coe_le_coe_iff]
