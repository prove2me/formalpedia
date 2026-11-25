-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.contDiffAt_phiM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:21:41.148004+00:00
-- url     : https://prove2.me/submissions/44f81b43-2809-499e-bf14-c10ac9f565b5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiffAt_zpow_lead

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
theorem _root_.solution (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n)
    {m : ℕ∞ω} : ContDiffAt ℂ m (PhiM μ) z := by
  unfold PhiM
  exact contDiffAt_prod fun i _ => contDiffAt_zpow_lead _ _ (hz i)
end ReciprocityTheory.ChartRestriction.DS.S7
