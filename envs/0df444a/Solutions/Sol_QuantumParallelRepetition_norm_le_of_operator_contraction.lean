-- Prove2me | solution 1 for QuantumParallelRepetition.norm_le_of_operator_contraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.787743+00:00
-- url     : https://prove2.me/submissions/12393bd0-ba0a-451c-b540-3e4427c75487

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace QuantumParallelRepetition
theorem _root_.solution
    (W : H →L[ℂ] H) (hW : ‖W‖ ≤ 1) (z : H) :
    ‖W z‖ ≤ ‖z‖ := by
  calc
    ‖W z‖ ≤ ‖W‖ * ‖z‖ := W.le_opNorm z
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hW (norm_nonneg z)
    _ = ‖z‖ := one_mul _
end QuantumParallelRepetition
