-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_finite_quot_e423b00c1db3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:02:41.186174+00:00
-- url     : https://prove2.me/submissions/b9b34b09-b017-46e5-86ae-b21272d6a9ea

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial DirectSum
noncomputable section
universe u
variable {S : Type u} [CommRing S] {N : ℕ}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (p : Ideal (Poly S N)) : Module.Finite (Poly S N) (Poly S N ⧸ p) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ (Poly S N) p).toLinearMap
    Ideal.Quotient.mk_surjective
end GroundTheory.Heights₂.Heights.Kleiman
