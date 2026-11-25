-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PSymplDetSchur_det_clearCol_b08499293871
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:46:00.400347+00:00
-- url     : https://prove2.me/submissions/facdc3b7-835d-4604-8cb9-008c44c4610d

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
theorem _root_.solution {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (clearCol A).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ ?_]
  · simp [clearCol]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    have hne : i ≠ j := ne_of_lt hij'
    have hj : j ≠ 0 := by
      rintro rfl
      simp at hij'
    simp [clearCol, hne, hj]
end GroundTheory.Heights₂.Heights.PSymplDetSchur
