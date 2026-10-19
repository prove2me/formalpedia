-- Prove2me | solution 1 for PermanentRollout.homogeneousIdeal_minimalPrime_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/6c22ab9d-7e06-42cb-84ce-c21ac24ac50c

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution {t : ℕ}
    (I P : Ideal (MvPolynomial (Fin t) ℂ))
    (hI : I.IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ))
    (hP : P ∈ I.minimalPrimes) :
    P.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin t) ℂ) := by
  let core := P.homogeneousCore
    (MvPolynomial.homogeneousSubmodule (Fin t) ℂ)
  have hcoreprime : core.toIdeal.IsPrime :=
    hP.isPrime.homogeneousCore
  have hcorele : core.toIdeal ≤ P :=
    Ideal.toIdeal_homogeneousCore_le
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ) P
  have hIcore : I ≤ core.toIdeal := by
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono
      (MvPolynomial.homogeneousSubmodule (Fin t) ℂ) hP.le
  have hreverse : P ≤ core.toIdeal :=
    hP.2 ⟨hcoreprime, hIcore⟩ hcorele
  have heq : core.toIdeal = P :=
    le_antisymm hcorele hreverse
  rw [← heq]
  exact core.isHomogeneous
end PermanentRollout
