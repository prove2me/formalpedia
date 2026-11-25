-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.norm_sq_le_pow_gs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:38:04.279799+00:00
-- url     : https://prove2.me/submissions/55c52c78-de75-448c-9535-87cc2ddc21ae

import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction
import Definitions.Def_ReciprocityTheory_ReducedBases_TBInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IntegralModuleBases_NormGsoSqLeTwoPowMulOfValEqAdd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_sum_lt_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_IntegralModuleBases_norm_sq_b
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_mu_of_lt
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_mu_self


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
theorem _root_.solution (b : Fin d → E) (hr : IsRed b) (i : Fin d) :
    ‖b i‖ ^ 2 ≤ 2 ^ i.val * ‖gs b i‖ ^ 2 := by
  have hb := hr.1
  rw [norm_sq_b b hb i]
  have hle : ∀ j ∈ (univ : Finset (Fin d)), mu b i j ^ 2 * ‖gs b j‖ ^ 2 ≤
      (if j < i then (1 / 4) * ‖gs b j‖ ^ 2 else 0) + (if j = i then ‖gs b i‖ ^ 2 else 0) := by
    intro j _
    rcases lt_trichotomy j i with h | h | h
    · have hm := hr.2.1 i j h
      have hq : mu b i j ^ 2 ≤ 1 / 4 := by
        nlinarith [abs_nonneg (mu b i j), sq_abs (mu b i j)]
      have := mul_le_mul_of_nonneg_right hq (sq_nonneg ‖gs b j‖)
      simp only [h, h.ne, if_true, if_false, add_zero]
      linarith
    · subst h; simp [mu_self b hb]
    · simp [mu_of_lt b h, h.ne', not_lt.mpr h.le]
  calc _ ≤ ∑ j, ((if j < i then (1 / 4) * ‖gs b j‖ ^ 2 else 0) + (if j = i then ‖gs b i‖ ^ 2 else 0)) :=
        sum_le_sum hle
    _ = (1 / 4) * ∑ j ∈ univ.filter (fun j : Fin d => j < i), ‖gs b j‖ ^ 2 + ‖gs b i‖ ^ 2 := by
        rw [sum_filter, mul_sum, sum_add_distrib]
        congr 1
        · apply sum_congr rfl; intro j _; split_ifs <;> ring
        · simp
    _ ≤ (1 / 4) * ((2 * 2 ^ i.val - 2) * ‖gs b i‖ ^ 2) + ‖gs b i‖ ^ 2 := by
        have := sum_lt_le b hr i; linarith
    _ ≤ 2 ^ i.val * ‖gs b i‖ ^ 2 := by
        have h1 : (1:ℝ) ≤ 2 ^ i.val := one_le_pow₀ (by norm_num)
        nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sq_nonneg ‖gs b i‖)]
end ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases
