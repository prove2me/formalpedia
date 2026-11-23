-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.LemK.tb_isUnit_of_omegaP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:10.944313+00:00
-- url     : https://prove2.me/submissions/38b0767c-33a2-4bd5-825c-2d7219dbc6c4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_KTypeLemma_TransferB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_LemK_tb_isUnit_of_omega

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.LemK
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK
theorem _root_.solution {x : Matrix (Fin n) (Fin n) ℂ} (hx : x ∈ OmegaP n) : IsUnit x := Matrix.isUnit_nonsing_inv_iff.mp (tb_isUnit_of_omega hx)
end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
