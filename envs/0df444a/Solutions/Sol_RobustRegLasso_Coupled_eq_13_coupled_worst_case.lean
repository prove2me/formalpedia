-- Prove2me | solution 1 for RobustRegLasso.Coupled.eq_13_coupled_worst_case
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:48:38.743418+00:00
-- url     : https://prove2.me/submissions/4fcd87ae-4214-457c-9cc7-9722a84f1127

import Mathlib
import Definitions.Def_RobustRegLasso_Coupled_Basic

set_option autoImplicit false
open RobustRegLasso.Coupled

theorem rrc_add_iSup {ι : Sort*} (a : ℝ) (g : ι → EReal) :
    (a : EReal) + ⨆ i, g i = ⨆ i, ((a : EReal) + g i) := by
  have hcont : Continuous (fun y : EReal => (a : EReal) + y) := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    have h := EReal.continuousAt_add (p := ((a : EReal), y)) (Or.inl (EReal.coe_ne_top a))
      (Or.inl (EReal.coe_ne_bot a))
    exact h.comp (f := fun y : EReal => ((a : EReal), y)) (by fun_prop)
  have hmono : Monotone (fun y : EReal => (a : EReal) + y) := fun x y hxy => add_le_add (le_refl _) hxy
  exact Monotone.map_iSup_of_continuousAt hcont.continuousAt hmono (by simp)

theorem rrc_matVec_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (a δ : Fin m → E) (x : Fin m → ℝ) : matVec (a + δ) x = matVec a x + matVec δ x := by
  simp [matVec, smul_add, Finset.sum_add_distrib]

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] {m k : ℕ} (a : Fin m → E) (b : E) (f : Fin k → (Fin m → ℝ) → ℝ)
    (hf : ∀ j, ConvexOn ℝ Set.univ (f j)) (x : Fin m → ℝ) :
    robustObjective a b (coupledSet f) x =
      ((‖b - matVec a x‖ : ℝ) : EReal) +
        ⨆ c ∈ budgetSet f, ((∑ i, |x i| * c i : ℝ) : EReal) := by
  set r : E := b - matVec a x with hr
  have hres : ∀ δ : Fin m → E, perturbedResidual a δ b x = ‖r - matVec δ x‖ := by
    intro δ
    simp only [perturbedResidual, rrc_matVec_add, hr]
    congr 1; abel
  apply le_antisymm
  · -- upper bound
    refine iSup₂_le fun δ hδ => ?_
    have hc : colNorms δ ∈ budgetSet f := ⟨hδ, fun i => norm_nonneg _⟩
    have h1 : perturbedResidual a δ b x ≤ ‖r‖ + ∑ i, |x i| * colNorms δ i := by
      rw [hres]
      calc ‖r - matVec δ x‖ ≤ ‖r‖ + ‖matVec δ x‖ := norm_sub_le _ _
        _ ≤ ‖r‖ + ∑ i, |x i| * colNorms δ i := by
          refine add_le_add (le_refl _) ?_
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, Real.norm_eq_abs]; rfl
    calc ((perturbedResidual a δ b x : ℝ) : EReal) ≤ ((‖r‖ + ∑ i, |x i| * colNorms δ i : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr h1
      _ = (‖r‖ : EReal) + ((∑ i, |x i| * colNorms δ i : ℝ) : EReal) := EReal.coe_add _ _
      _ ≤ (‖r‖ : EReal) + ⨆ c ∈ budgetSet f, ((∑ i, |x i| * c i : ℝ) : EReal) := by
          refine add_le_add (le_refl _) ?_
          exact le_iSup₂ (f := fun c (_ : c ∈ budgetSet f) => ((∑ i, |x i| * c i : ℝ) : EReal))
            (colNorms δ) hc
  · -- lower bound
    rw [rrc_add_iSup]
    refine iSup_le fun c => ?_
    rw [rrc_add_iSup]
    refine iSup_le fun hc => ?_
    obtain ⟨hcZ, hc0⟩ := hc
    obtain ⟨u, hu1, hru⟩ : ∃ u : E, ‖u‖ = 1 ∧ r = ‖r‖ • u := by
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
    have hnorm : colNorms δ = c := by
      funext i
      simp only [colNorms, hδ, norm_smul, hu1, mul_one, Real.norm_eq_abs, abs_neg, abs_mul, hsg1,
        abs_of_nonneg (hc0 i)]
    have hδU : δ ∈ coupledSet f := by
      intro j; rw [hnorm]; exact hcZ j
    have hmv : matVec δ x = (-(∑ i, |x i| * c i)) • u := by
      simp only [matVec, hδ, smul_smul]
      rw [← Finset.sum_smul, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hxsg i]; ring
    have hS : 0 ≤ ∑ i, |x i| * c i := Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hc0 i)
    have hval : perturbedResidual a δ b x = ‖r‖ + ∑ i, |x i| * c i := by
      rw [hres, hmv]
      have : r - (-(∑ i, |x i| * c i)) • u = (‖r‖ + ∑ i, |x i| * c i) • u := by
        conv_lhs => rw [hru]
        rw [neg_smul, sub_neg_eq_add, ← add_smul]
      rw [this, norm_smul, hu1, mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (‖r‖ : EReal) + ((∑ i, |x i| * c i : ℝ) : EReal)
        = ((perturbedResidual a δ b x : ℝ) : EReal) := by rw [hval, EReal.coe_add]
      _ ≤ ⨆ δ ∈ coupledSet f, ((perturbedResidual a δ b x : ℝ) : EReal) :=
          le_iSup₂ (f := fun δ (_ : δ ∈ coupledSet f) => ((perturbedResidual a δ b x : ℝ) : EReal)) δ hδU
