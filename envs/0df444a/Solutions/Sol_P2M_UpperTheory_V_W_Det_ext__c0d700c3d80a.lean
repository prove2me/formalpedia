-- Prove2me | solution 1 for P2M_UpperTheory_V_W_Det_ext__c0d700c3d80a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:14:17.374341+00:00
-- url     : https://prove2.me/submissions/cc09f0d0-3aa1-4014-9fbc-3ae407c1627b

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_RepAlg
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnopSMul
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_CommutativeAlgebraHeight_OfDetToDet

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
open UpperTheory.V.W.Det
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
namespace UpperTheory.V.W.Det
theorem _root_.solution {D D' : Det n A E} (h : ∀ (S : Type) [CommRing S] [Algebra A S] (x), D.D S x = D'.D S x) : D = D' := by
  cases D; cases D'; congr; funext S _ _; exact MonoidHom.ext (h S)
end UpperTheory.V.W.Det
