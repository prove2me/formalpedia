-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.realTrace_toMatrix_mul_toMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:17:24.228484+00:00
-- url     : https://prove2.me/submissions/1fdae60a-f6db-4a1d-8bea-0773893e5c6b

import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_QuditBounds
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_realTrace_toMatrix

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
open QEC.Semantics.FiniteMatrixEntropy
namespace QEC.Semantics.FiniteMatrixEntropy
theorem _root_.solution
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {n : Type v} [Fintype n] [DecidableEq n]
    (b : OrthonormalBasis n Complex H) (A X : Operator H) :
    realTrace (A.toMatrix b.toBasis b.toBasis * X.toMatrix b.toBasis b.toBasis) =
      Complex.re (LinearMap.trace Complex H (A.comp X)) := by
  rw [← LinearMap.toMatrix_comp]
  exact realTrace_toMatrix b (A.comp X)
end QEC.Semantics.FiniteMatrixEntropy
