-- Prove2me | solution 1 for P2M_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_dop_sb__0996b08225dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:00:01.843432+00:00
-- url     : https://prove2.me/submissions/e371a440-23c6-4de3-8bc2-ce912f3adcb8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_wdb_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
namespace ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
theorem _root_.solution {n : ℕ} (j k : Fin n) (g : Fin 4 → V n → ℂ) (a b : V n → ℂ) (h0 : g 0 = a)
    (h1 : g 1 = a) (h2 : g 2 = b) (h3 : g 3 = b) (y : V n) :
    B.Dop cS (vS n j k) g y = wdb n j a y - wdb n k b y := by
  simp [B.Dop, Fin.sum_univ_four, cS, vS, wdb_eq, h0, h1, h2, h3]
  ring
end ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
