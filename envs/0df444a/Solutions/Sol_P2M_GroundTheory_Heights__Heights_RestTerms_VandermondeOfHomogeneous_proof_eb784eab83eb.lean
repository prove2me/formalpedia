-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_VandermondeOfHomogeneous_proof_eb784eab83eb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:53:51.010014+00:00
-- url     : https://prove2.me/submissions/2bf8adfa-c430-45a0-ad05-4fce4f6884cf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PVandermondeOfHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_VandermondeOfHomogeneous_sum_card_Ioi_77f69092f923

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
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace VandermondeOfHomogeneous
theorem _root_.solution : VandermondeOfHomogeneous.Statement := by
  intro σ R _ m v hv
  rw [← VandermondeOfHomogeneous.sum_card_Ioi m]
  unfold vandermondeOf
  refine IsHomogeneous.prod _ _ _ fun i _ => ?_
  refine IsHomogeneous.prod _ _ _ fun j _ => ?_
  exact (hv i).sub (hv j)
end VandermondeOfHomogeneous
end GroundTheory.Heights₂.Heights.RestTerms
