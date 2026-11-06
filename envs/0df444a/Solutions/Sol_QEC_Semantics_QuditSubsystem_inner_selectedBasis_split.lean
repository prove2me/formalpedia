-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.inner_selectedBasis_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:46:04.557493+00:00
-- url     : https://prove2.me/submissions/65c3904b-4949-47ad-916b-007e81469fe3

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedFactorization_apply_basis

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (x y : Qudit.Label T.selectedDimensions) :
    inner Complex (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex y)
        (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex x) =
      inner Complex
          (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
            (S.splitSelectedLabel T hST y).1)
          (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex
            (S.splitSelectedLabel T hST x).1) *
        inner Complex
          (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
            (S.splitSelectedLabel T hST y).2)
          (EuclideanSpace.basisFun (Qudit.Label (S.additionalRetainedDimensions T)) Complex
            (S.splitSelectedLabel T hST x).2) := by
  rw [← (S.selectedFactorization T hST).map_inner]
  rw [S.selectedFactorization_apply_basis T hST y,
    S.selectedFactorization_apply_basis T hST x]
  rw [TensorProduct.inner_tmul]
end QEC.Semantics.QuditSubsystem
