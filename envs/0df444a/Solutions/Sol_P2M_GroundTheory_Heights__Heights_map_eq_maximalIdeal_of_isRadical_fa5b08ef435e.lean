-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_map_eq_maximalIdeal_of_isRadical_fa5b08ef435e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:42.867808+00:00
-- url     : https://prove2.me/submissions/e79022d1-ec92-40e1-91e9-dab1f2835942

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical

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
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {A : Type*} [CommRing A] {J W : Ideal A} [W.IsPrime]
    (hJ : J.IsRadical) (hW : W ∈ J.minimalPrimes) :
    J.map (algebraMap A (Localization.AtPrime W)) = IsLocalRing.maximalIdeal (Localization.AtPrime W) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W (Localization.AtPrime W),
    ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime W) W J hW,
    ← IsLocalization.map_radical W.primeCompl (Localization.AtPrime W) J, hJ.radical]
end GroundTheory.Heights₂.Heights
