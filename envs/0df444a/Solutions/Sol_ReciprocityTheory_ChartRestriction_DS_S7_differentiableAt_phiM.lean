-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.differentiableAt_phiM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:28:59.679497+00:00
-- url     : https://prove2.me/submissions/71cb556c-7b95-481d-8904-9d3280a49862

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiffAt_phiM

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
theorem _root_.solution (μ : Fin n → ℤ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    DifferentiableAt ℂ (PhiM μ) z := by
  exact (contDiffAt_phiM μ hz (m := 1)).differentiableAt (by norm_num)
end ReciprocityTheory.ChartRestriction.DS.S7
