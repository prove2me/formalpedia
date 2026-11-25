-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplDetBound_proof_75776b7928b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:04.879411+00:00
-- url     : https://prove2.me/submissions/d0ed8b63-49d1-4c74-852f-cbec2327f398

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplDetBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplDetBound_step_bound_847aa8cffc89

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
open Matrix
namespace GroundTheory.Heights₂.Heights
namespace SymplDetBound
theorem _root_.solution (h1 : SymplStep.Statement) : SymplDetBound.Statement := by
  intro n
  induction n with
  | zero =>
    intro G _ _
    refine ⟨1, Submonoid.one_mem _, ?_⟩
    rw [Matrix.det_isEmpty]
    simp
  | succ n ih =>
    intro G hG hpos
    obtain ⟨ρsq, _, _, hle, P, hP, _, hdet⟩ :=
      h1 n ((2 * (n : ℝ)) ^ n) G hG hpos (fun H hH hHpos => ih H hH hHpos)
    exact ⟨P, hP, hdet.trans (PSymplDetBound.step_bound n ρsq hle)⟩
end SymplDetBound
end GroundTheory.Heights₂.Heights
