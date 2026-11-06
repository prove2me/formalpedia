-- Prove2me | solution 1 for QEC.Semantics.FiniteMatrixEntropy.realTrace_toMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:45:43.096443+00:00
-- url     : https://prove2.me/submissions/8504e514-54fe-441a-8493-4e1c704191e3

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
theorem _root_.solution
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] {n : Type v} [Fintype n] [DecidableEq n]
    (b : OrthonormalBasis n Complex H) (A : Operator H) :
    realTrace (A.toMatrix b.toBasis b.toBasis) =
      Complex.re (LinearMap.trace Complex H A) := by
  unfold realTrace
  rw [← LinearMap.trace_eq_matrix_trace Complex b.toBasis A]
end QEC.Semantics.FiniteMatrixEntropy
