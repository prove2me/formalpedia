-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFiniteGradedQuotient_finrank_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.983104+00:00
-- url     : https://prove2.me/submissions/d48170ae-d70c-41e8-9975-605de2e7f33d

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
    {ι : Type*} [Finite ι] (I : Ideal (MvPolynomial ι ℂ))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι ℂ))
    (N : ℕ)
    (hhigh : ∀ n : ℕ, N ≤ n →
      ∀ p : MvPolynomial ι ℂ, p.IsHomogeneous n → p ∈ I) :
    Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I) =
      ∑ i : Fin N,
        Module.finrank ℂ (homogeneousMapGradedQuotientPiece I i) := by
  classical
  letI (i : Fin N) :
      Module.Finite ℂ (MvPolynomial.homogeneousSubmodule ι ℂ (i : ℕ)) :=
    (Submodule.fg_iff_finiteDimensional _).mp
      (MvPolynomial.homogeneousSubmodule_fg ι ℂ i)
  letI (i : Fin N) :
      Module.Finite ℂ (homogeneousMapGradedQuotientPiece I i) :=
    inferInstance
  letI (i : Fin N) :
      Module.Free ℂ (homogeneousMapGradedQuotientPiece I i) :=
    Module.Free.of_divisionRing ℂ (homogeneousMapGradedQuotientPiece I i)
  let E := homogeneousMapFiniteGradedQuotientEquiv I hI N hhigh
  calc
    Module.finrank ℂ (MvPolynomial ι ℂ ⧸ I) =
        Module.finrank ℂ
          ((i : Fin N) → homogeneousMapGradedQuotientPiece I i) :=
      E.finrank_eq.symm
    _ = ∑ i : Fin N,
        Module.finrank ℂ (homogeneousMapGradedQuotientPiece I i) :=
      Module.finrank_pi_fintype ℂ
end PermanentRollout
