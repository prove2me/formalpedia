-- Prove2me | solution 1 for ThreeSum1960614.threeSum_1960614
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-14T05:20:16.884984+00:00
-- url     : https://prove2.me/submissions/17448ceb-49aa-4f37-9e4e-107b286f0059

-- Reduction to two genuinely open published children, not a closed machine proof.
import Theorems.Thm_ThreeSum1960614_quartic_parameter_certificate
import Theorems.Thm_ThreeSum1960614_costs_solve_3sum

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem solution : EndStatement.ThreeSum.SolvedInTime 1.960614 := by
  apply ThreeSum1960614.costs_solve_3sum (1.960614 : ℚ) (by norm_num)
  obtain ⟨_, _, _, _, _, _, _, _, _, hcost, hgap⟩ :=
    ThreeSum1960614.quartic_parameter_certificate
  intro z hz
  have htarget : principal < (1.960614 : ℝ) := by
    norm_num [target] at hgap ⊢
    exact hgap
  exact (hcost z hz).trans htarget
