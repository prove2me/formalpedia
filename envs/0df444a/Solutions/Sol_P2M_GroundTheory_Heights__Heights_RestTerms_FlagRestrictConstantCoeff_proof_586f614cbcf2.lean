-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagRestrictConstantCoeff_proof_586f614cbcf2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:08:26.780859+00:00
-- url     : https://prove2.me/submissions/4a5f2a4a-07f6-46a1-bf1e-fa5ab49dd564

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagRestrictConstantCoeff

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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagRestrictConstantCoeff
theorem _root_.solution : FlagRestrictConstantCoeff.Statement := by
  intro f N τ R
  induction R using MvPolynomial.induction_on with
  | C a => simp [restrictToBlock]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp, constantCoeff_X, mul_zero]
    have hX : constantCoeff (restrictToBlock f N τ (X i)) = 0 := by
      simp only [restrictToBlock, aeval_X]
      split_ifs <;> simp
    rw [hX, mul_zero]
end FlagRestrictConstantCoeff
end GroundTheory.Heights₂.Heights.RestTerms
