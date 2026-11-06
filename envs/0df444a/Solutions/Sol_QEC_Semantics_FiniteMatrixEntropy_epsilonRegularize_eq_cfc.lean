-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.epsilonRegularize_eq_cfc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:50:06.141248+00:00
-- url     : https://prove2.me/submissions/7ac8d8df-e51e-4a74-87f6-9471ce5865ab

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution {n : Type v} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.IsHermitian) (epsilon : Real) :
    epsilonRegularize B epsilon = hB.cfc (fun x =>
      (1 + epsilon * Fintype.card n)⁻¹ * (x + epsilon)) := by
  unfold epsilonRegularize epsilonRegularizationDenominator
  rw [← hB.cfc_eq]
  change (1 + epsilon * Fintype.card n)⁻¹ • (B + epsilon • 1) =
    cfc (fun x : Real => (1 + epsilon * Fintype.card n)⁻¹ • (x + epsilon)) B
  have hsmul :
      cfc (fun x : Real => (1 + epsilon * Fintype.card n)⁻¹ • (x + epsilon)) B =
        (1 + epsilon * Fintype.card n)⁻¹ • cfc (fun x : Real => x + epsilon) B := by
    exact cfc_smul (p := IsSelfAdjoint) (1 + epsilon * Fintype.card n)⁻¹
      (fun x : Real => x + epsilon) B
  have hadd : cfc (fun x : Real => x + epsilon) B = B + epsilon • 1 := by
    rw [cfc_add_const epsilon (fun x : Real => x) B]
    have hid : cfc (fun x : Real => x) B = B :=
      cfc_id' (p := IsSelfAdjoint) (R := Real) B hB
    rw [hid]
    rw [Algebra.algebraMap_eq_smul_one (A := Matrix n n Complex)]
  rw [hsmul, hadd]
end QEC.Semantics.FiniteMatrixEntropy
