-- Prove2me | solution 1 for UpperTheory.V.W.GDet.ofDet_toDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:35:21.929212+00:00
-- url     : https://prove2.me/submissions/926d0fe2-61f2-4352-ae6f-1ec9e261598b

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_RepAlg
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnopSMul
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebraHeight_OfDetToDet
import Theorems.Thm_UpperTheory_V_W_ofT_toT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing
open UpperTheory UpperTheory.V UpperTheory.V.W
open UpperTheory.V.W.GDet
variable {n : ℕ} {A G : Type} [CommRing A] [Group G]
namespace UpperTheory.V.W.GDet
theorem _root_.solution (D : GDet n A G) : ofDet D.toDet = D :=
  GDet.ext fun S _ _ x => congrArg (D.D S) (ofT_toT (A := A) x)
end UpperTheory.V.W.GDet
