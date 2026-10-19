-- Prove2me | solution 1 for PermanentRollout.homogeneousMapGradedQuotientMulLinearMap_finrank_quotient_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/2cbef373-04ca-46f6-8db7-4507f4324335

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMapGradedQuotientMulLinearMap_injective_iff
import Theorems.Thm_PermanentRollout_homogeneousMapGradedQuotientMulLinearMap_finrank_quotient_add_kernel

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped nonZeroDivisors Pointwise
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [Finite ι] (I : Ideal (MvPolynomial ι ℂ))
    (f : MvPolynomial ι ℂ) {e : ℕ} (hf : f.IsHomogeneous e) (n : ℕ)
    (hcolon : ∀ p : MvPolynomial.homogeneousSubmodule ι ℂ n,
      f * (p : MvPolynomial ι ℂ) ∈ I →
        (p : MvPolynomial ι ℂ) ∈ I) :
    Module.finrank ℂ
        (homogeneousMapGradedQuotientPiece I (e + n) ⧸
          LinearMap.range
            (homogeneousMapGradedQuotientMulLinearMap I f hf n)) +
      Module.finrank ℂ (homogeneousMapGradedQuotientPiece I n) =
        Module.finrank ℂ (homogeneousMapGradedQuotientPiece I (e + n)) := by
  have hinj :=
    (homogeneousMapGradedQuotientMulLinearMap_injective_iff
      I f hf n).mpr hcolon
  have hker :
      LinearMap.ker
        (homogeneousMapGradedQuotientMulLinearMap I f hf n) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have hkerfin :
      Module.finrank ℂ
        (LinearMap.ker
          (homogeneousMapGradedQuotientMulLinearMap I f hf n)) = 0 := by
    rw [hker]
    exact finrank_bot ℂ _
  have hrec :=
    homogeneousMapGradedQuotientMulLinearMap_finrank_quotient_add_kernel
      I f hf n
  omega
end PermanentRollout
