-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalCompleteProjectiveOutcome_eq_blockVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/82c41f2c-0a7b-495c-8511-fd67d2541eda

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : ℕ} (w : ℝ) (N : ℕ)
    (ξ ζ : BipartiteUnitVector d) (a b : Bool) :
    dSVDensityRationalCompleteProjectiveOutcome
        w N ξ ζ a b =
      (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) •
        toLp 2
          (Matrix.vec
            ((Matrix.blockDiagonal' fun k : Fin N =>
              (dSVDensityRationalLeftProjectiveThresholdPOVM
                  w N k ξ).effect a *
                (dSVDensityRationalLeftProjectiveThresholdPOVM
                  w N k ζ).effect b).transpose)) := by
  classical
  rw [dSVDensityRationalCompleteProjectiveOutcome_eq_block_action]
  let τ : Fin N → ℝ := fun _ => 1
  let P : Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun k => (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ξ).effect a
  let R : Fin N → Matrix (Fin d) (Fin d) ℂ :=
    fun k => (dSVDensityRationalLeftProjectiveThresholdPOVM
      w N k ζ).effect b
  let M : Matrix
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d)
      (DSVUniformDensityThresholdLocalIndex N d ×
        DSVUniformDensityThresholdLocalIndex N d) ℂ :=
    Matrix.blockDiagonal' P ⊗ₖ
      (Matrix.blockDiagonal' R).transpose
  change
    Matrix.toEuclideanLin M
      (sharedThresholdResource (d := Fin d) τ) = _
  rw [sharedThresholdResource,
    (Matrix.toEuclideanLin M).map_smul_of_tower]
  congr 1
  have raw := sharedThresholdResourceRaw_block_action τ P R
  change
    toLp 2
      (M.mulVec
        (ofLp (sharedThresholdResourceRaw (d := Fin d) τ))) =
      toLp 2
        (Matrix.vec
          ((Matrix.blockDiagonal' fun k : Fin N => P k * R k).transpose))
  simpa only [M, P, R, τ, Complex.ofReal_one, one_smul] using raw
end QuantumParallelRepetition
