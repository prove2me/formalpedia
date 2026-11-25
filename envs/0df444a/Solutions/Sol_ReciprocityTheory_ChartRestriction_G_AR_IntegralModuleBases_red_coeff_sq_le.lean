-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.red_coeff_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:44.526401+00:00
-- url     : https://prove2.me/submissions/557dad79-77bd-4efa-a67f-457867d3ea7f

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_gs_sq_ge
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_coeff_bound
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_norm_sq_comb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
open Finset InnerProductSpace ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
theorem _root_.solution (b : Fin d → E) (hr : IsRed b) (m : ℝ) (hm0 : 0 < m)
    (hm : ∀ i, m ≤ ‖b i‖ ^ 2) (c : Fin d → ℝ) (i : Fin d) :
    c i ^ 2 ≤ 9 ^ d * ‖∑ l, c l • b l‖ ^ 2 / m := by
  have hb := hr.1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ‖∑ l, c l • b l‖ ^ 2 := ⟨_, rfl⟩
  rw [← hX]
  have hX0 : 0 ≤ X := by rw [hX]; exact sq_nonneg _
  have hp : (0:ℝ) < 2 ^ (d - 1) := by positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = X * 2 ^ (d - 1) / m := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; exact div_nonneg (mul_nonneg hX0 hp.le) hm0.le
  have hnu : ∀ j, |nu b c j| ≤ Real.sqrt y := by
    intro j
    apply Real.abs_le_sqrt
    have h1 : nu b c j ^ 2 * ‖gs b j‖ ^ 2 ≤ X := by
      rw [hX, norm_sq_comb b hb c]
      exact Finset.single_le_sum (f := fun j => nu b c j ^ 2 * ‖gs b j‖ ^ 2)
        (fun k _ => by positivity) (mem_univ j)
    have h2 := gs_sq_ge b hr m hm j
    have h3 : nu b c j ^ 2 * (m / 2 ^ (d - 1)) ≤ X :=
      le_trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) h1
    rw [hy, le_div_iff₀ hm0]
    have h4 : nu b c j ^ 2 * (m / 2 ^ (d - 1)) * 2 ^ (d - 1) = nu b c j ^ 2 * m := by
      rw [mul_assoc, div_mul_cancel₀ _ hp.ne']
    nlinarith [mul_le_mul_of_nonneg_right h3 hp.le]
  have hc := coeff_bound b hb hr.2.1 c (Real.sqrt_nonneg y) hnu i
  have hsq : c i ^ 2 ≤ ((3 / 2 : ℝ) ^ d * Real.sqrt y) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  rw [mul_pow, Real.sq_sqrt hy0] at hsq
  have h1 : ((3 / 2 : ℝ) ^ d) ^ 2 * 4 ^ d = 9 ^ d := by
    rw [← pow_mul, mul_comm d 2, pow_mul, ← mul_pow]; norm_num
  have h2 : (2:ℝ) ^ (d - 1) ≤ 4 ^ d :=
    calc (2:ℝ) ^ (d - 1) ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      _ ≤ 4 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hA : ((3 / 2 : ℝ) ^ d) ^ 2 * 2 ^ (d - 1) ≤ 9 ^ d :=
    calc _ ≤ ((3 / 2 : ℝ) ^ d) ^ 2 * 4 ^ d := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 9 ^ d := h1
  calc c i ^ 2 ≤ ((3 / 2 : ℝ) ^ d) ^ 2 * y := hsq
    _ = (((3 / 2 : ℝ) ^ d) ^ 2 * 2 ^ (d - 1)) * X / m := by rw [hy]; ring
    _ ≤ 9 ^ d * X / m := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA hX0) hm0.le
end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
