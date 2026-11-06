-- Prove2me | solution 1 for QEC.Semantics.OperatorMatrix.scalarMatrix_quadratic_eq_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:32:34.479804+00:00
-- url     : https://prove2.me/submissions/04729775-a242-464d-b3ff-b31c01f06ce2

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.OperatorMatrix
variable {n : Nat} {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.OperatorMatrix
theorem _root_.solution {β : Type*} [Fintype β]
    (M : OperatorMatrix n H) (b : OrthonormalBasis β Complex H)
    (c : Fin n × β → Complex) :
    dotProduct (star c) ((scalarMatrix M b).mulVec c) =
      ∑ i : Fin n, ∑ j : Fin n,
        inner Complex (M i j (∑ q : β, star (c (j, q)) • b q))
          (∑ p : β, star (c (i, p)) • b p) := by
  classical
  let F : Fin n → β → Fin n → β → Complex :=
    fun i p j q => c (j, q) * (inner Complex (M i j (b q)) (b p) * star (c (i, p)))
  calc
    dotProduct (star c) ((scalarMatrix M b).mulVec c) =
        ∑ i : Fin n, ∑ p : β, ∑ j : Fin n, ∑ q : β, F i p j q := by
      simp [F, scalarMatrix, dotProduct, Matrix.mulVec, Fintype.sum_prod_type,
        Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ p : β, ∑ q : β, F i p j q := by
      apply Finset.sum_congr rfl
      intro _i _hi
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        inner Complex (M i j (∑ q : β, star (c (j, q)) • b q))
          (∑ p : β, star (c (i, p)) • b p) := by
      simp [F, map_sum, Finset.sum_mul, mul_assoc, mul_comm]
end QEC.Semantics.OperatorMatrix
