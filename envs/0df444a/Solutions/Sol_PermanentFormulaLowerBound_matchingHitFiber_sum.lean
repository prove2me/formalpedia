-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingHitFiber_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/fd471998-7a71-476d-880a-4f83ff708276

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingEmbedding_prod_split

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {F : Type*} [CommSemiring F]
    {ell m : ℕ} (p : Fin m → F) {P : Finset (Fin ell)}
    (u : ↥P) (b : Fin m) :
    (∑ rho : {rho : ↥P ↪ Fin m // rho u = b},
      ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) =
        p b ^ (2 ^ (u.1 : ℕ)) *
          matchingAvoidingInjectionSum p (P.erase u.1) b := by
  classical
  calc
    (∑ rho : {rho : ↥P ↪ Fin m // rho u = b},
      ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) =
        ∑ rho : (↥(P.erase u.1) ↪ {j : Fin m // j ≠ b}),
          p b ^ (2 ^ (u.1 : ℕ)) *
            ∏ v : ↥(P.erase u.1), p (rho v).1 ^ (2 ^ (v.1 : ℕ)) := by
              refine Fintype.sum_equiv (matchingHitEmbeddingEquiv u b) _ _ ?_
              intro rho
              exact matchingEmbedding_prod_split p u b rho.1 rho.2
    _ = p b ^ (2 ^ (u.1 : ℕ)) *
          matchingAvoidingInjectionSum p (P.erase u.1) b := by
            simp [matchingAvoidingInjectionSum, Finset.mul_sum]
end PermanentFormulaLowerBound
