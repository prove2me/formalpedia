-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_CombAfterPower_zero_d69257a99942
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:34.997428+00:00
-- url     : https://prove2.me/submissions/b5c35791-60ef-4dfa-88a8-e8d34022331f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericNoetherNormalisation
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SumRMulNe
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ProofSimp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericNoetherNormalisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Polynomial MvPolynomial Ideal Nat RingHom List
open GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {m : ℕ}
variable {c : A} {z : Fin m → D} {s : Finset D}
namespace GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
namespace CombAfterPower
theorem _root_.solution : CombAfterPower c z s 0 :=
  ⟨0, fun _ ↦ 0, by simp⟩
end CombAfterPower
end GroundTheory.Heights₂.Heights.GenericNoetherNormalisation
