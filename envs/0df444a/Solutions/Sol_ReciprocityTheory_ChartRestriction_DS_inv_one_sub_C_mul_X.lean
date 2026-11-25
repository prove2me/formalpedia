-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.inv_one_sub_C_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:31:18.184407+00:00
-- url     : https://prove2.me/submissions/4e0e27b6-24e2-46b2-9f1f-9f8cf749b0c7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (c : ℂ) :
    (1 - PowerSeries.C c * PowerSeries.X)⁻¹ = PowerSeries.mk (fun k => c ^ k) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, mul_comm (PowerSeries.mk _) (PowerSeries.C c), mul_assoc]
  cases n with
  | zero => simp
  | succ n =>
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), pow_succ]
    ring
end ReciprocityTheory.ChartRestriction.DS
