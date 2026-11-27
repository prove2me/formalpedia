-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_isotropic_gramIso_7ab060123dc5
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:19:18.865134+00:00
-- url     : https://prove2.me/submissions/59e189f5-2481-4516-8fbe-dc06a147f6b6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Automorphic Matrix
theorem _root_.solution : (![1, 1] : Fin 2 → GaussQ) ≠ 0 ∧ gaussValue gramIso ![1, 1] = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · have := congrFun h 0
    simp at this
  · first
    | simp [gaussValue, gramIso, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
    | (unfold gaussValue gramIso; simp [Fin.sum_univ_two])



