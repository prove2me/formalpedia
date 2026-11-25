-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsLiftToZeros_exists_extend_c6312c5192ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:32:19.674057+00:00
-- url     : https://prove2.me/submissions/4ab92444-bdf0-49d1-a61b-6c2e8d9335a0

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qi28_exists_extend__36ded2848554
import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsLiftToZeros
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsMoreRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootsLiftToZeros

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace RootsLiftToZeros
theorem _root_.solution {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] (ev : R →+* ℂ) (hker : RingHom.ker (algebraMap R A) ≤ RingHom.ker ev) :
    ∃ χ : A →+* ℂ, χ.comp (algebraMap R A) = ev :=
  _root_.P2M_UpperTheory_Reformulated_B_Qi28_exists_extend__36ded2848554 ev hker
end RootsLiftToZeros
end GroundTheory.Heights₂.Heights.HilbertSamuel
