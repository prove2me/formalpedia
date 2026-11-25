-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_constantCoeff_powerSumHom_cd225d5dc115
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:08.699515+00:00
-- url     : https://prove2.me/submissions/9b3e6a52-682b-4e6c-91d5-0069b7f0c571

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums

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
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (N : ℕ) (S : MvPolynomial (Fin N) ℚ) :
    constantCoeff (powerSumHom N S) = constantCoeff S := by
  induction S using MvPolynomial.induction_on with
  | C a => simp [powerSumHom]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, powerSumHom, aeval_X, constantCoeff_X, mul_zero]
    simp [psum, constantCoeff_X]
end GroundTheory.Heights₂.Heights.RestTerms.Flag
