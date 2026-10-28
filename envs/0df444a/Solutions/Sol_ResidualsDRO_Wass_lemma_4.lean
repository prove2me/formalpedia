-- Prove2me | solution 1 for ResidualsDRO.Wass.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:53:56.45874+00:00
-- url     : https://prove2.me/submissions/84131b57-6907-4a17-aa1b-46b18e3d8e25

import Mathlib
import Definitions.Def_ResidualsDRO_Wass_Setting

open MeasureTheory

open ResidualsDRO.Wass in
theorem solution {dx dy n : ℕ} (hn : 1 ≤ n) (p : ℝ) (hp : 1 ≤ p)
    (fstar fhat : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (xs : Fin n → EuclideanSpace ℝ (Fin dx)) (eps : Fin n → EuclideanSpace ℝ (Fin dy))
    (x : EuclideanSpace ℝ (Fin dx)) :
    powerMean p (fun i => ‖epsTilde fstar fhat xs eps x i‖) ≤
      ‖fstar x - fhat x‖ + powerMean p (fun i => ‖fstar (xs i) - fhat (xs i)‖) := by
  set c := ‖fstar x - fhat x‖ with hc
  set b : Fin n → ℝ := fun i => ‖fstar (xs i) - fhat (xs i)‖ with hb
  have hnorm : ∀ i, ‖epsTilde fstar fhat xs eps x i‖ ≤ c + b i := by
    intro i
    have e : epsTilde fstar fhat xs eps x i =
        (fhat x - fstar x) + (fstar (xs i) - fhat (xs i)) := by
      unfold epsTilde ResidualsDRO.Wass.residual
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_sub_rev]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 < p := by linarith
  have hq : 0 ≤ 1 / p := by positivity
  have hc0 : 0 ≤ c := norm_nonneg _
  have hb0 : ∀ i, 0 ≤ b i := fun i => norm_nonneg _
  have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn'.le
  have hS1 : 0 ≤ ∑ i : Fin n, (c + b i) ^ p :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (by linarith [hb0 i]) p)
  have hS2 : 0 ≤ ∑ i : Fin n, b i ^ p :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hb0 i) p)
  have e1 : ((n : ℝ)⁻¹ * ∑ i : Fin n, b i ^ p) ^ (1 / p) =
      (n : ℝ)⁻¹ ^ (1 / p) * (∑ i : Fin n, b i ^ p) ^ (1 / p) := Real.mul_rpow hinv hS2
  have e2 : (n : ℝ)⁻¹ ^ (1 / p) * (∑ _i : Fin n, c ^ p) ^ (1 / p) = c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Real.mul_rpow hn'.le (Real.rpow_nonneg hc0 p), one_div, Real.rpow_rpow_inv hc0 hp0.ne',
      ← mul_assoc, ← Real.mul_rpow hinv hn'.le, inv_mul_cancel₀ hn'.ne', Real.one_rpow, one_mul]
  unfold powerMean
  calc ((n : ℝ)⁻¹ * ∑ i, ‖epsTilde fstar fhat xs eps x i‖ ^ p) ^ (1 / p)
      ≤ ((n : ℝ)⁻¹ * ∑ i : Fin n, (c + b i) ^ p) ^ (1 / p) := by
        apply Real.rpow_le_rpow
        · exact mul_nonneg hinv (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) p))
        · apply mul_le_mul_of_nonneg_left _ hinv
          exact Finset.sum_le_sum (fun i _ => Real.rpow_le_rpow (norm_nonneg _) (hnorm i) hp0.le)
        · exact hq
    _ = (n : ℝ)⁻¹ ^ (1 / p) * (∑ i : Fin n, (c + b i) ^ p) ^ (1 / p) := Real.mul_rpow hinv hS1
    _ ≤ (n : ℝ)⁻¹ ^ (1 / p) * ((∑ _i : Fin n, c ^ p) ^ (1 / p) + (∑ i : Fin n, b i ^ p) ^ (1 / p)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hinv _)
        exact Real.Lp_add_le_of_nonneg Finset.univ hp (fun _ _ => hc0) (fun i _ => hb0 i)
    _ = c + ((n : ℝ)⁻¹ * ∑ i : Fin n, b i ^ p) ^ (1 / p) := by
        rw [mul_add, e2, e1]
