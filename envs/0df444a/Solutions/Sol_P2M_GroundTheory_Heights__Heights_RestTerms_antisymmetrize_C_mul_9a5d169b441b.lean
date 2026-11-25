-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_antisymmetrize_C_mul_9a5d169b441b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:11:56.166849+00:00
-- url     : https://prove2.me/submissions/a57064f4-5f80-45a1-b083-a2491892c175

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AltPush
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PLemmaB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms
theorem _root_.solution (f N : ℕ) (k : ℚ) (H : RootRing f N) :
    antisymmetrize f N (C k * H) = C k * antisymmetrize f N H := by
  unfold antisymmetrize
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [blockPermute]
end GroundTheory.Heights₂.Heights.RestTerms
