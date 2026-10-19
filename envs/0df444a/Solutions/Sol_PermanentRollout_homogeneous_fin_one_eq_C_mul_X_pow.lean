-- Prove2me | solution 1 for PermanentRollout.homogeneous_fin_one_eq_C_mul_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/fa01bea5-36a5-4001-9609-65f3939c1c69

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_MvPolynomial_IsWeightedHomogeneous_eq_monomial_of_unique_weight_tenProofs

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace PermanentRollout
theorem _root_.solution
    {f : MvPolynomial (Fin 1) ℂ} {e : ℕ}
    (hf : f.IsHomogeneous e) :
    f =
      MvPolynomial.C
          (MvPolynomial.coeff (Finsupp.single (0 : Fin 1) e) f) *
        MvPolynomial.X 0 ^ e := by
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  apply MvPolynomial.IsWeightedHomogeneous.eq_monomial_of_unique_weight_tenProofs hf
  intro a ha
  apply Finsupp.ext
  intro i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  have hdegree : a.degree = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact ha
  simpa [Finsupp.degree_eq_sum] using hdegree
end PermanentRollout
