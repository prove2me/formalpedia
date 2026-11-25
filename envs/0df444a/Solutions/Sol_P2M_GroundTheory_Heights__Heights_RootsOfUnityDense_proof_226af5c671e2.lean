-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RootsOfUnityDense_proof_226af5c671e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:54.39645+00:00
-- url     : https://prove2.me/submissions/52800a7e-3bdd-440d-8b4c-dce71009e3b3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootsOfUnityDense
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootsOfUnityDenseAlt_rootsOfUnity_infinite_fb3881bcacd7

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
namespace GroundTheory.Heights₂.Heights
namespace RootsOfUnityDense
theorem _root_.solution : RootsOfUnityDense.Statement := by
  intro n P hP
  refine MvPolynomial.funext_set (p := P) (q := 0)
    (fun _ => {z : ℂ | ∃ k : ℕ, 0 < k ∧ z ^ k = 1})
    (fun _ => RootsOfUnityDenseAlt.rootsOfUnity_infinite) ?_
  intro x hx
  rw [map_zero]
  exact hP x fun i => hx i (Set.mem_univ i)
end RootsOfUnityDense
end GroundTheory.Heights₂.Heights
