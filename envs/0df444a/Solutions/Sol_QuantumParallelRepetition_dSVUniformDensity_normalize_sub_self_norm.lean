-- Prove2me | solution 1 for QuantumParallelRepetition.dSVUniformDensity_normalize_sub_self_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/75e54071-4aef-4e5c-9fe7-dd0b34f929b8

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : ℕ} (v : EuclideanSpace ℂ (Fin d × Fin d))
    (nonzero : v ≠ 0) :
    ‖NormedSpace.normalize v - v‖ = |1 - ‖v‖| := by
  have positive : 0 < ‖v‖ := norm_pos_iff.mpr nonzero
  calc
    ‖NormedSpace.normalize v - v‖ =
        ‖((‖v‖⁻¹ - 1 : ℝ) • v)‖ := by
          unfold NormedSpace.normalize
          congr 1
          rw [sub_smul, one_smul]
    _ = |‖v‖⁻¹ - 1| * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs]
    _ = |(‖v‖⁻¹ - 1) * ‖v‖| := by
          rw [abs_mul, abs_of_nonneg (norm_nonneg v)]
    _ = |1 - ‖v‖| := by
          congr 1
          field_simp [positive.ne']
end QuantumParallelRepetition
