-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.intw_fouInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:59.767675+00:00
-- url     : https://prove2.me/submissions/cc214ee4-5bd4-4eea-8c3c-d2416003cbb2

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_intw_fou

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution (p q : Eu l) : Intw (fouInv l) p q q (-p) := fun f g h => by
  funext x
  have h1 := congrFun (intw_fou p q f g h) (-x)
  have e : ∀ (u : Sch l) y, fouInv l u y = fou l u (-y) := fun u y => rfl
  rw [e, h1]
  simp only [rf, e, inner_neg_left, inner_neg_right, neg_add]
end PositivityTheory.ThKR.LL
