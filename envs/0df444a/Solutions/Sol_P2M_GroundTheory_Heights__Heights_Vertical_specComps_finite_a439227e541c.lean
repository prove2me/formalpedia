-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_specComps_finite_a439227e541c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:59.104723+00:00
-- url     : https://prove2.me/submissions/e26d3d19-04c1-4c52-a4a6-3200c35f78ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_POrdEq

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
    (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) : (specComps I v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1
end GroundTheory.Heights₂.Heights.Vertical
