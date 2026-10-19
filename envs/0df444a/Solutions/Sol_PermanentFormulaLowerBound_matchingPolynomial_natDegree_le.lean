-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPolynomial_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/40e8bb9a-c1d1-4378-90e2-7875a3c7b70d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPolynomial_of_nonempty
import Theorems.Thm_PermanentFormulaLowerBound_matchingBinaryDegree_erase_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {F : Type*} [CommRing F] [Nontrivial F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) :
    (matchingPolynomial p P).natDegree ≤ matchingBinaryDegree P := by
  classical
  refine Finset.strongInductionOn P ?_
  intro P ih
  by_cases hP : P.Nonempty
  · rw [matchingPolynomial_of_nonempty p P hP]
    apply (Polynomial.natDegree_sub_le_of_le
      (m := matchingBinaryDegree P) (n := matchingBinaryDegree P) ?_ ?_).trans
      (by simp)
    · simp
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro u _
      calc
        ((Polynomial.X : Polynomial F) ^ (2 ^ (u.1 : ℕ)) *
          matchingPolynomial p (P.erase u.1)).natDegree
            ≤ 2 ^ (u.1 : ℕ) + matchingBinaryDegree (P.erase u.1) :=
              Polynomial.natDegree_mul_le_of_le
                (by simp) (ih (P.erase u.1) (Finset.erase_ssubset u.property))
        _ = matchingBinaryDegree P := by
          rw [Nat.add_comm, matchingBinaryDegree_erase_add P u.1 u.property]
  · have h_empty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    subst P
    simp
end PermanentFormulaLowerBound
