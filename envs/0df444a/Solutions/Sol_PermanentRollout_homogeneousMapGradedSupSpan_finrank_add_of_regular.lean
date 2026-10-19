-- Prove2me | solution 1 for PermanentRollout.homogeneousMapGradedSupSpan_finrank_add_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/f299ae16-ebb0-41f3-9488-25c71fc2df24

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMapGradedQuotientMulLinearMap_finrank_quotient_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped BigOperators
open scoped BigOperators
open scoped Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι]
    (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ))
    (f : MvPolynomial ι ℂ) {e : ℕ}
    (hf : f.IsHomogeneous e)
    (hregular : IsSMulRegular (MvPolynomial ι ℂ ⧸ I) f)
    (n : ℕ) :
    Module.finrank ℂ
        (homogeneousMapGradedQuotientPiece
          (I ⊔ Ideal.span {f}) (e + n)) +
      Module.finrank ℂ (homogeneousMapGradedQuotientPiece I n) =
      Module.finrank ℂ
        (homogeneousMapGradedQuotientPiece I (e + n)) := by
  have hcolon : ∀ p : MvPolynomial.homogeneousSubmodule ι ℂ n,
      f * (p : MvPolynomial ι ℂ) ∈ I →
        (p : MvPolynomial ι ℂ) ∈ I := by
    intro p hp
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem I f).mp hregular
      (p : MvPolynomial ι ℂ)
    simpa [smul_eq_mul] using hp
  have hrec := homogeneousMapGradedQuotientMulLinearMap_finrank_quotient_add
    I f hf n hcolon
  have hequiv :=
    (homogeneousMapGradedSupSpanQuotientEquivCokernel
      I hI f hf n).finrank_eq
  rw [hequiv] at hrec
  exact hrec
end PermanentRollout
