-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CapPhi.negE_apply_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:36.786666+00:00
-- url     : https://prove2.me/submissions/0a611b4c-46f3-4975-92b8-2b939f2fe2a7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiCapelliStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPhiA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_Central
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CapPhi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
namespace ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
theorem _root_.solution (a b : Fin n) (G : smoothS n) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∉ OmegaSet n) :
    ((negE a b G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z = 0 := by
  exact ltOp_of_not_mem _ hz
end ReciprocityTheory.ChartRestriction.DS.S7.CapPhi
