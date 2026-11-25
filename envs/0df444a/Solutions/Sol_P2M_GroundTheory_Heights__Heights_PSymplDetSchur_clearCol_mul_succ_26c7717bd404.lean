-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplDetSchur_clearCol_mul_succ_26c7717bd404
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:58.159797+00:00
-- url     : https://prove2.me/submissions/8f85c1e0-dee8-49ec-a1b9-5cc834b58a1f

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin n)
    (j : Fin (n + 1)) :
    (clearCol A * A) i.succ j = A i.succ j - A i.succ 0 / A 0 0 * A 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp [clearCol, Fin.succ_ne_zero, Fin.succ_inj]
  ring
end GroundTheory.Heights₂.Heights.PSymplDetSchur
