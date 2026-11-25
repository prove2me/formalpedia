-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplDetSchur_clearCol_mul_zero_2d45a2bc5e4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:59.206846+00:00
-- url     : https://prove2.me/submissions/60c4fa6a-ff9f-4f0a-8826-69e798850acc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplDetSchur

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
open GroundTheory.Heights₂.Heights.PSymplDetSchur
namespace GroundTheory.Heights₂.Heights.PSymplDetSchur
theorem _root_.solution {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin (n + 1)) :
    (clearCol A * A) 0 j = A 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp [clearCol, (Fin.succ_ne_zero _).symm, Fin.succ_ne_zero]
end GroundTheory.Heights₂.Heights.PSymplDetSchur
