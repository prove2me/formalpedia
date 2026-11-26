-- Prove2me | solution 1 for Sendov.one_le_integral_prod_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:16:33.57481+00:00
-- url     : https://prove2.me/submissions/3dc4f65d-10c5-43c3-90eb-582d730918a6

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
import Theorems.Thm_Sendov_norm_sub_le_norm_one_sub_mul
import Theorems.Thm_Sendov_prod_map_le_of_le
import Theorems.Thm_Sendov_norm_prod_map
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero



set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : |a| ≤ 1)
    {z q : Multiset ℂ} (hz : ∀ w ∈ z, ‖w‖ ≤ 1)
    (hpolar : q.prod * (z.map (fun w => 1 - (a : ℂ) * w)).prod
      = (n : ℂ) * ∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod)
    (hdenom : q.prod * (z.map (fun w => (a : ℂ) - w)).prod = (n : ℂ)) :
    1 ≤ ∫ t in (0 : ℝ)..1,
        (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  -- the Möbius estimate, multiplied over the multiset
  have hmob : (z.map (fun w => ‖(a : ℂ) - w‖)).prod
      ≤ (z.map (fun w => ‖1 - (a : ℂ) * w‖)).prod :=
    prod_map_le_of_le (fun w hw => norm_sub_le_norm_one_sub_mul ha (hz w hw))
  -- take norms in the two identities
  have h1 : (n : ℝ) = ‖q.prod‖ * (z.map (fun w => ‖(a : ℂ) - w‖)).prod := by
    have := congrArg (fun w : ℂ => ‖w‖) hdenom
    simpa [norm_mul, norm_prod_map] using this.symm
  have h2 : ‖q.prod‖ * (z.map (fun w => ‖1 - (a : ℂ) * w‖)).prod
      = (n : ℝ) * ‖∫ t in (0 : ℝ)..1,
          (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
    have := congrArg (fun w : ℂ => ‖w‖) hpolar
    simpa [norm_mul, norm_prod_map] using this
  -- so the integral has norm at least one
  have h3 : (1 : ℝ) ≤ ‖∫ t in (0 : ℝ)..1,
      (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
    have hstep : (n : ℝ) ≤ (n : ℝ) * ‖∫ t in (0 : ℝ)..1,
        (q.map (fun v => (a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v)).prod‖ := by
      rw [← h2, h1]
      exact mul_le_mul_of_nonneg_left hmob (norm_nonneg _)
    nlinarith [hstep, hnpos]
  -- and the triangle inequality moves the norm inside
  refine h3.trans ?_
  refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans_eq ?_
  refine intervalIntegral.integral_congr ?_
  intro t _
  simp only []
  exact norm_prod_map q _
end Sendov
