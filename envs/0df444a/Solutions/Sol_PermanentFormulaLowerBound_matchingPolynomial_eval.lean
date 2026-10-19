-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPolynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/0e3232eb-ee49-49a5-a0fa-dde62ada7b1a

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingPolynomial_of_nonempty
import Theorems.Thm_PermanentFormulaLowerBound_matchingInjectionSum_partition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {F : Type*} [CommRing F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) (b : Fin m) :
    (matchingPolynomial p P).eval (p b) =
      matchingAvoidingInjectionSum p P b := by
  classical
  refine Finset.strongInductionOn P ?_
  intro P ih
  by_cases hP : P.Nonempty
  · rw [matchingPolynomial_of_nonempty p P hP, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_finsetSum]
    simp_rw [Polynomial.eval_mul, Polynomial.eval_X_pow]
    have hterms :
        (∑ u : ↥P,
          p b ^ (2 ^ (u.1 : ℕ)) *
            (matchingPolynomial p (P.erase u.1)).eval (p b)) =
          ∑ u : ↥P,
            p b ^ (2 ^ (u.1 : ℕ)) *
              matchingAvoidingInjectionSum p (P.erase u.1) b := by
      apply Finset.sum_congr rfl
      intro u _
      rw [ih (P.erase u.1) (Finset.erase_ssubset u.property)]
    rw [hterms, matchingInjectionSum_partition p P b]
    simp
  · have h_empty : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    subst P
    simp
end PermanentFormulaLowerBound
