-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplDetSchur_proof_32fd04616391
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:06.234005+00:00
-- url     : https://prove2.me/submissions/6a1cb18c-170f-4967-aa4a-ad68628147a2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplDetSchur
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplDetSchur_det_clearCol_b08499293871
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplDetSchur_clearCol_mul_zero_2d45a2bc5e4e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplDetSchur_clearCol_mul_succ_26c7717bd404

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
open PSymplDetSchur
namespace GroundTheory.Heights₂.Heights
namespace SymplDetSchur
theorem _root_.solution : SymplDetSchur.Statement := by
  intro n A ha
  have hdet : A.det = (clearCol A * A).det := by
    rw [Matrix.det_mul, det_clearCol, one_mul]
  rw [hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hcol : ∀ i : Fin n, (clearCol A * A) i.succ 0 = 0 := by
    intro i
    rw [clearCol_mul_succ]
    field_simp
    ring
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero, clearCol_mul_zero]
  congr 1
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, clearCol_mul_succ]
  ring
end SymplDetSchur
end GroundTheory.Heights₂.Heights
