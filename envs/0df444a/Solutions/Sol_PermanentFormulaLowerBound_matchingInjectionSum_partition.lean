-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingInjectionSum_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/bf13120d-70fd-4e89-a707-052450a022ee

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_matchingHitFiber_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution {F : Type*} [CommSemiring F]
    {ell m : ℕ} (p : Fin m → F) (P : Finset (Fin ell)) (b : Fin m) :
    matchingInjectionSum p P =
      matchingAvoidingInjectionSum p P b +
        ∑ u : ↥P,
          p b ^ (2 ^ (u.1 : ℕ)) *
            matchingAvoidingInjectionSum p (P.erase u.1) b := by
  classical
  have havoid :
      (∑ rho : {rho : ↥P ↪ Fin m // ∀ u, rho u ≠ b},
        ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) =
          matchingAvoidingInjectionSum p P b := by
    unfold matchingAvoidingInjectionSum
    refine Fintype.sum_equiv (matchingAvoidingEmbeddingEquiv b) _ _ ?_
    intro rho
    rfl
  have hhit :
      (∑ rho : {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b},
        ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) =
          ∑ u : ↥P,
            ∑ rho : {rho : ↥P ↪ Fin m // rho u = b},
              ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ)) := by
    calc
      (∑ rho : {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b},
        ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) =
          ∑ rho : (Σ u : ↥P, {rho : ↥P ↪ Fin m // rho u = b}),
            ∏ v : ↥P, p (rho.2.1 v) ^ (2 ^ (v.1 : ℕ)) := by
              refine Fintype.sum_equiv (matchingHitSigmaEquiv b) _ _ ?_
              intro rho
              rfl
      _ = ∑ u : ↥P,
            ∑ rho : {rho : ↥P ↪ Fin m // rho u = b},
              ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ)) :=
            Fintype.sum_sigma _
  calc
    matchingInjectionSum p P =
        (∑ rho : {rho : ↥P ↪ Fin m // ∀ u, rho u ≠ b},
          ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) +
        (∑ rho : {rho : ↥P ↪ Fin m // ¬ ∀ u, rho u ≠ b},
          ∏ v : ↥P, p (rho.1 v) ^ (2 ^ (v.1 : ℕ))) := by
            simpa only [matchingInjectionSum] using
              (Fintype.sum_subtype_add_sum_subtype
                (fun rho : ↥P ↪ Fin m => ∀ u, rho u ≠ b)
                (fun rho => ∏ v : ↥P,
                  p (rho v) ^ (2 ^ (v.1 : ℕ)))).symm
    _ = matchingAvoidingInjectionSum p P b +
        ∑ u : ↥P,
          p b ^ (2 ^ (u.1 : ℕ)) *
            matchingAvoidingInjectionSum p (P.erase u.1) b := by
              rw [havoid, hhit]
              congr 1
              apply Finset.sum_congr rfl
              intro u _
              exact matchingHitFiber_sum p u b
end PermanentFormulaLowerBound
