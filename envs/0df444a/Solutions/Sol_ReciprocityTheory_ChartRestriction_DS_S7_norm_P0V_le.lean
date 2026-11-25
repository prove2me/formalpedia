-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.norm_P0V_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:46.052943+00:00
-- url     : https://prove2.me/submissions/f30fb69d-4d1d-42d1-a668-e382fb36d8d3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hsRV_P0V_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hsRV_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) (s : Bool) : ‖signedIdentityColumns ε s‖ ≤ Real.sqrt n := by
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt (by rw [← hsRV_eq]; exact hsRV_P0V_le ε s))
end ReciprocityTheory.ChartRestriction.DS.S7
