-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ComplexSets_coneProj_mem_orthoRows_4bca22bd21ba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:52:39.661327+00:00
-- url     : https://prove2.me/submissions/f3177e66-f4cf-4625-b8ef-bfaa438b38a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial Pointwise
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.ComplexSets
theorem _root_.solution : coneProj ∈ orthoRows 2 3 := by
  show coneProj * coneProj.conjTranspose = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coneProj, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply]
end GroundTheory.Heights₂.Heights.ComplexSets
