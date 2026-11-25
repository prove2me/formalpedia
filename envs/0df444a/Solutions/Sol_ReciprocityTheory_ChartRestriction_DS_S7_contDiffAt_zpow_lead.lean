-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.contDiffAt_zpow_lead
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:15:08.091187+00:00
-- url     : https://prove2.me/submissions/cee699f8-b7ba-40a8-aeb1-f76c435e465b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiff_lead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (i : ℕ) (k : ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : lead i z ≠ 0)
    {m : ℕ∞ω} : ContDiffAt ℂ m (fun w => lead i w ^ k) z := by
  have hl : ContDiffAt ℂ m (lead (n := n) i) z := (contDiff_lead i).contDiffAt
  rcases k with k | k
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact hl.pow k
  · simp only [zpow_negSucc]
    exact (hl.pow (k + 1)).inv (pow_ne_zero _ hz)
end ReciprocityTheory.ChartRestriction.DS.S7
