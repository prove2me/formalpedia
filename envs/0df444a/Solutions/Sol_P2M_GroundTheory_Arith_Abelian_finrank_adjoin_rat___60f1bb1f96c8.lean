-- Prove2me | solution 1 for P2M_GroundTheory_Arith_Abelian_finrank_adjoin_rat___60f1bb1f96c8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:51:02.879328+00:00
-- url     : https://prove2.me/submissions/c0208bb1-9c18-4bf0-8a71-d400413962cd

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
universe u
variable {F : Type u} [Field F]
variable (E : WeierstrassCurve F) [E.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {n : ℤ} (hn : n ≠ 0) :
    Module.finrank (IntermediateField.adjoin F {ratΦΨ E n}) (RatFunc F) = n.natAbs ^ 2 := by
  rw [RatFunc.finrank_eq_max_natDegree, max_natDegree_ratΦΨ E hn]
end GroundTheory.Arith.Abelian
