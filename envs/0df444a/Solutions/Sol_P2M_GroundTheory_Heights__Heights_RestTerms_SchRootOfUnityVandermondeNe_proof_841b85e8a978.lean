-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_SchRootOfUnityVandermondeNe_proof_841b85e8a978
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:53:56.64413+00:00
-- url     : https://prove2.me/submissions/1b09be3a-6f84-48b6-9156-44a8a12a9af4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchRootOfUnityVandermondeNe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchRootOfUnityVandermondeNe_rootOfUnity_isPrimitiveRoot_6f2807b96c51

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
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace SchRootOfUnityVandermondeNe
theorem _root_.solution : SchRootOfUnityVandermondeNe.Statement := by
  intro k hk
  have hz := SchRootOfUnityVandermondeNe.rootOfUnity_isPrimitiveRoot hk
  unfold vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  rw [sub_ne_zero]
  intro h
  have hij : (i : ℕ) = j := hz.pow_inj i.isLt j.isLt h
  have hlt : i < j := Finset.mem_Ioi.mp hj
  exact absurd (Fin.ext hij) (ne_of_lt hlt)
end SchRootOfUnityVandermondeNe
end GroundTheory.Heights₂.Heights.RestTerms
