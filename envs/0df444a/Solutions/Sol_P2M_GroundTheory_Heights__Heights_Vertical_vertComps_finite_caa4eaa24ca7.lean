-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_vertComps_finite_caa4eaa24ca7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:07.9503+00:00
-- url     : https://prove2.me/submissions/9608e928-7400-477b-9d84-d64d7b4f0066

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PVertTermEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
theorem _root_.solution {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (vertComps I u v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1.1
end GroundTheory.Heights₂.Heights.Vertical
