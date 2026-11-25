-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_locMap_injective_d760537304b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:02:55.186589+00:00
-- url     : https://prove2.me/submissions/96776c3e-432e-434d-ab59-5ffb2608261d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCechDSq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDegLocExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCechExact

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
open MvPolynomial
noncomputable section
universe u v
universe w
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
omit [Module S M] [IsScalarTower S (Poly S N) M] [Module S M'] [IsScalarTower S (Poly S N) M']
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (f : M →ₗ[Poly S N] M') (hf : Function.Injective f)
    (I : Finset (Fin (N + 1))) : Function.Injective (locMap f I) :=
  by
    unfold locMap
    exact IsLocalizedModule.map_injective (S := monos (S := S) I)
      (f := LocalizedModule.mkLinearMap (monos (S := S) I) M)
      (g := LocalizedModule.mkLinearMap (monos (S := S) I) M') (h_inj := hf)
end GroundTheory.Heights₂.Heights.Kleiman
