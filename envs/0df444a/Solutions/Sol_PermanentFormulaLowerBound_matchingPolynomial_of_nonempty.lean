-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingPolynomial_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/433b6c75-fe1f-4ee8-8348-eeeeaed463e2

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {F : Type*} [CommRing F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell))
    (hP : P.Nonempty) :
    matchingPolynomial p P =
      Polynomial.C (matchingInjectionSum p P) -
        ∑ u : ↥P,
          (Polynomial.X : Polynomial F) ^ (2 ^ (u.1 : ℕ)) *
            matchingPolynomial p (P.erase u.1) := by
  rw [matchingPolynomial]
  simp [hP]
end PermanentFormulaLowerBound
