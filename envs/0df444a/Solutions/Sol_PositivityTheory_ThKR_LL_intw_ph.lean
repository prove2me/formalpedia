-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.intw_ph
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:41.608129+00:00
-- url     : https://prove2.me/submissions/9b1d4d2b-9430-4e8e-9a1a-030ebdc4aff4

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Theorems.Thm_PositivityTheory_ThKR_LL_ph_apply

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
theorem _root_.solution {S : Eu l →L[ℝ] Eu l} (hS : ∀ x y, ⟪x, S y⟫ = ⟪y, S x⟫) (p q : Eu l) : Intw (ph S) p q p (q + S p) :=
  fun f g h => by
    funext x
    simp only [rf, ph_apply, h, ← mul_assoc, ← Complex.exp_add]
    congr 2
    rw [← add_mul, ← add_mul, ← ofReal_add, ← ofReal_add]
    congr 2
    simp only [inner_add_left, inner_add_right, map_add, hS p x, real_inner_comm x (S p)]
    ring
end PositivityTheory.ThKR.LL
