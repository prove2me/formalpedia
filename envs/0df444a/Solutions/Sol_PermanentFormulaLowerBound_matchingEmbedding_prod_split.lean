-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingEmbedding_prod_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/380ce917-cef7-4847-ac05-490f2f211a2b

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {F : Type*} [CommSemiring F]
    {ell m : ℕ} (p : Fin m → F) {P : Finset (Fin ell)}
    (u : ↥P) (b : Fin m) (rho : ↥P ↪ Fin m) (hrho : rho u = b) :
    (∏ v : ↥P, p (rho v) ^ (2 ^ (v.1 : ℕ))) =
      p b ^ (2 ^ (u.1 : ℕ)) *
        ∏ v : ↥(P.erase u.1),
          p ((matchingEraseEmbedding u b rho hrho) v).1 ^
            (2 ^ (v.1 : ℕ)) := by
  classical
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun v : ↥P => p (rho v) ^ (2 ^ (v.1 : ℕ))) u, hrho]
  congr 1
  refine Fintype.prod_equiv (matchingEraseIndexEquiv u) _ _ ?_
  intro v
  rfl
end PermanentFormulaLowerBound
