-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPolynomial_coeff_binaryDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/c74c7f36-4fcc-4206-bcdf-79e44d84bc1d

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPolynomial_of_nonempty
import Theorems.Thm_PermanentFormulaLowerBound_matchingBinaryDegree_erase_add
import Theorems.Thm_PermanentFormulaLowerBound_matchingBinaryDegree_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {F : Type*} [CommRing F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) :
    (matchingPolynomial p P).coeff (matchingBinaryDegree P) =
      (-1 : F) ^ P.card * (P.card.factorial : F) := by
  classical
  refine Finset.strongInductionOn P ?_
  intro P ih
  by_cases hP : P.Nonempty
  · have hD : matchingBinaryDegree P ≠ 0 :=
      (matchingBinaryDegree_pos P hP).ne'
    have hterm (u : ↥P) :
        ((Polynomial.X : Polynomial F) ^ (2 ^ (u.1 : ℕ)) *
          matchingPolynomial p (P.erase u.1)).coeff (matchingBinaryDegree P) =
            (-1 : F) ^ (P.card - 1) * ((P.card - 1).factorial : F) := by
      rw [← matchingBinaryDegree_erase_add P u.1 u.property,
        Polynomial.coeff_X_pow_mul,
        ih (P.erase u.1) (Finset.erase_ssubset u.property),
        Finset.card_erase_of_mem u.property]
    rw [matchingPolynomial_of_nonempty p P hP, Polynomial.coeff_sub,
      Polynomial.coeff_C_of_ne_zero hD]
    simp_rw [Polynomial.finsetSum_coeff, hterm]
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hP.card_ne_zero
    rw [hr]
    simp [hr, Nat.factorial_succ, pow_succ, nsmul_eq_mul,
      mul_assoc, mul_comm]
    ac_rfl
  · have h_empty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    subst P
    simp
end PermanentFormulaLowerBound
