-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagIntegralVandermondePos_proof_b66617cfa28f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:08:38.032939+00:00
-- url     : https://prove2.me/submissions/84cf25b2-4683-4509-8ba7-4a5b08121525

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagIntegralVandermondePos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockVandermonde_ne_zero_737fbd71d1a2


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
namespace FlagIntegralVandermondePos
theorem _root_.solution : FlagIntegralVandermondePos.Statement := by
  intro f N
  unfold flagIntegral
  have hne : (blockVandermonde f N).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact Flag.blockVandermonde_ne_zero f N
  refine Finset.sum_pos (fun α hα => ?_) hne
  have hc : coeff α (blockVandermonde f N) ≠ 0 := mem_support_iff.mp hα
  refine mul_pos (mul_self_pos.mpr hc) ?_
  unfold Finsupp.prod
  exact Finset.prod_pos fun i _ => by simp only; exact_mod_cast Nat.factorial_pos _
end FlagIntegralVandermondePos
end GroundTheory.Heights₂.Heights.RestTerms
