-- Prove2me | solution 1 for PermanentRollout.homogeneousMapGradedQuotientMulLinearMap_injective_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/df409a3c-74df-4f50-8e92-4ce5e84abdac

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} (I : Ideal (MvPolynomial ι ℂ))
    (f : MvPolynomial ι ℂ) {e : ℕ} (hf : f.IsHomogeneous e) (n : ℕ) :
    Function.Injective (homogeneousMapGradedQuotientMulLinearMap I f hf n) ↔
      ∀ p : MvPolynomial.homogeneousSubmodule ι ℂ n,
        f * (p : MvPolynomial ι ℂ) ∈ I →
          (p : MvPolynomial ι ℂ) ∈ I := by
  constructor
  · intro hinj p hp
    have hmul :
        (homogeneousMapGradedQuotientMulLinearMap I f hf n)
          (Submodule.Quotient.mk p) = 0 := by
      change Submodule.Quotient.mk
        (homogeneousPolynomialMulLinearMap f hf n p) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact hp
    have hz :
        (Submodule.Quotient.mk p : homogeneousMapGradedQuotientPiece I n) = 0 :=
      hinj (hmul.trans (map_zero _).symm)
    change p ∈ homogeneousMapGradedIdealPiece I n
    exact (Submodule.Quotient.mk_eq_zero
      (homogeneousMapGradedIdealPiece I n)).mp hz
  · intro hcolon
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ p =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      apply hcolon
      change Submodule.Quotient.mk
        (homogeneousPolynomialMulLinearMap f hf n p) = 0 at hx
      change homogeneousPolynomialMulLinearMap f hf n p ∈
        homogeneousMapGradedIdealPiece I (e + n)
      exact (Submodule.Quotient.mk_eq_zero
        (homogeneousMapGradedIdealPiece I (e + n))).mp hx
end PermanentRollout
