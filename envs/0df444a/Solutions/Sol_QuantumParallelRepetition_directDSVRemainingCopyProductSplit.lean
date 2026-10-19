-- Prove2me | solution 1 for QuantumParallelRepetition.directDSVRemainingCopyProductSplit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/23feabbe-0b94-4273-961e-f1dc679f84d3

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
    {M : Type*} [CommMonoid M]
    {L : ℕ} (j : Fin L) (f : Fin L → M) :
    (∏ i : Fin L, f i) =
      (∏ i : Fin j.val, f ⟨i.val, by omega⟩) *
      (∏ i : Fin (L - j.val),
        f ⟨j.val + i.val, by omega⟩) := by
  classical
  have length : j.val + (L - j.val) = L := by omega
  calc
    (∏ i : Fin L, f i) =
        ∏ i : Fin (j.val + (L - j.val)), f (i.cast length) :=
      (Fin.prod_congr' f length).symm
    _ =
        (∏ i : Fin j.val, f ⟨i.val, by omega⟩) *
        (∏ i : Fin (L - j.val),
          f ⟨j.val + i.val, by omega⟩) := by
      rw [Fin.prod_univ_add]
      congr 1
end QuantumParallelRepetition
