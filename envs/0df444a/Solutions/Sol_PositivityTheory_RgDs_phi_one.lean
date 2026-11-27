-- Prove2me | solution 1 for PositivityTheory.RgDs.phi_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:18.034498+00:00
-- url     : https://prove2.me/submissions/a6ef0111-b581-4606-b28f-6673f647bd87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_DiscreteSeries_DiscreteSeriesCovers_ExplicitFunctionSquareIntegrable

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
open PositivityTheory PositivityTheory.RgDs
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
namespace PositivityTheory.RgDs
theorem _root_.solution : phi (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold phi lead
  refine Finset.prod_eq_one fun i _ => ?_
  rw [dif_pos (Nat.succ_le_of_lt i.2)]
  simp [Matrix.submatrix_one _ (Fin.castLE_injective _)]
end PositivityTheory.RgDs
