-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceTensorEmbezzlementOne_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/56767ba6-8a83-42a5-b50c-960957abe6fa

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceEmbezzlementOne_apply

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (finCongr (Nat.mul_one d))
          (finCongr (Nat.mul_one d)))
        (tensorEmbezzlementTarget (n := 1) ξ) = ξ.val := by
  classical
  ext ⟨i, j⟩
  have first :
      (((finCongr (Nat.mul_one d)).symm i).divNat : Fin d) = i := by
    apply Fin.ext
    change i.val / 1 = i.val
    simp
  have second :
      (((finCongr (Nat.mul_one d)).symm j).divNat : Fin d) = j := by
    apply Fin.ext
    change j.val / 1 = j.val
    simp
  have first_work :
      (((finCongr (Nat.mul_one d)).symm i).modNat : Fin 1) = 0 :=
    Subsingleton.elim _ _
  have second_work :
      (((finCongr (Nat.mul_one d)).symm j).modNat : Fin 1) = 0 :=
    Subsingleton.elim _ _
  change
    ξ.val
        ((((finCongr (Nat.mul_one d)).symm i).divNat : Fin d),
         (((finCongr (Nat.mul_one d)).symm j).divNat : Fin d)) *
      embezzlementState 1
        ((((finCongr (Nat.mul_one d)).symm i).modNat : Fin 1),
         (((finCongr (Nat.mul_one d)).symm j).modNat : Fin 1)) =
      ξ.val (i, j)
  rw [first, second, first_work, second_work,
    unconditionalActualFairSourceEmbezzlementOne_apply, mul_one]
end QuantumParallelRepetition
