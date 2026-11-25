-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_C_mul_e0cd3fab3f15
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:12:22.602981+00:00
-- url     : https://prove2.me/submissions/1ba26e27-6545-4f63-8f8f-53cd901803d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsElem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Elementary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsElem

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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (f N : ℕ) (b : ℚ) (Φ : RootRing f N) :
    flagIntegral f N (C b * Φ) = b * flagIntegral f N Φ := by
  simp only [flagIntegral, coeff_C_mul, Finset.mul_sum, mul_assoc]
end GroundTheory.Heights₂.Heights.RestTerms
