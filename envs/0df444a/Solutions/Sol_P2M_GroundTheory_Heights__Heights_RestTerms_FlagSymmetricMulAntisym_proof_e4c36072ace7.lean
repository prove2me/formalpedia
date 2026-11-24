-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagSymmetricMulAntisym_proof_e4c36072ace7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:10:27.256894+00:00
-- url     : https://prove2.me/submissions/8269eead-81ea-469f-82e4-4f7ad0b3f9bf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagSymmetricMulAntisym

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
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagSymmetricMulAntisym
theorem _root_.solution : FlagSymmetricMulAntisym.Statement := by
  intro f N P H hP
  unfold antisymmetrize
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [map_mul, hP w, mul_smul_comm]
end FlagSymmetricMulAntisym
end GroundTheory.Heights₂.Heights.RestTerms
