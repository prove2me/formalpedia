-- Prove2me | solution 1 for PermanentFormulaLowerBound.matchingCrossWeight_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:13.22648+00:00
-- url     : https://prove2.me/submissions/56f7ee3b-fa2f-428e-8c0f-d9a407060b69

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentFormulaLowerBound_sum_matchingCrossPermutation_rows_cols
import Theorems.Thm_PermanentFormulaLowerBound_matchingPolynomial_eval
import Theorems.Thm_PermanentFormulaLowerBound_matching_card_omitted_external
import Theorems.Thm_PermanentFormulaLowerBound_matching_leftWeightedAvoidingInjectionSum
import Theorems.Thm_PermanentFormulaLowerBound_matching_rightWeightedAvoidingInjectionSum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentFormulaLowerBound
universe u v w
open scoped BigOperators Kronecker Matrix IntermediateField.algebraAdjoinAdjoin
namespace PermanentFormulaLowerBound
theorem _root_.solution
    {F : Type*} [CommRing F] {ell m : ℕ}
    (p q : Fin m → F) (P Q : Finset (Fin ell)) (a b : Fin m) :
    (∑ σ : MatchingCrossPermutation (↥P ⊕ ↥Q)
      {j : Fin m // j ≠ a} {j : Fin m // j ≠ b},
        matchingCrossWeight p q P Q a b σ) =
      (matchingJacobianWeight m P.card Q.card : F) *
        ((matchingPolynomial p P).eval (p b) *
          (matchingPolynomial q Q).eval (q a)) := by
  classical
  let wp : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}) → F :=
    fun rho => ∏ u : ↥P,
      p (rho (.inl u)).1 ^ (2 ^ (u.1 : ℕ))
  let wq : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}) → F :=
    fun theta => ∏ v : ↥Q,
      q (theta (.inr v)).1 ^ (2 ^ (v.1 : ℕ))
  have hcard :
      Fintype.card {j : Fin m // j ≠ a} =
        Fintype.card {j : Fin m // j ≠ b} :=
    (matching_card_omitted_external a).trans
      (matching_card_omitted_external b).symm
  have hfact :
      (Fintype.card {j : Fin m // j ≠ a} -
        Fintype.card (↥P ⊕ ↥Q)).factorial =
          (m - 1 - P.card - Q.card).factorial := by
    rw [matching_card_omitted_external]
    have hsum : Fintype.card (↥P ⊕ ↥Q) = P.card + Q.card := by
      simp
    rw [hsum]
    congr 1
    omega
  have hsplit :
      (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}),
        ∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}),
          wp rho * wq theta) =
        (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}), wp rho) *
          (∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}), wq theta) := by
    calc
      (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}),
        ∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}),
          wp rho * wq theta) =
        ∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}),
          wp rho *
            (∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}),
              wq theta) := by
            apply Finset.sum_congr rfl
            intro rho _
            rw [Finset.mul_sum]
      _ = (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}), wp rho) *
          (∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}),
            wq theta) := by
            rw [Finset.sum_mul]
  have hleft :
      (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}), wp rho) =
        ((m - 1 - P.card).descFactorial Q.card : F) *
          (matchingPolynomial p P).eval (p b) := by
    calc
      (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}), wp rho) =
          ((m - 1 - P.card).descFactorial Q.card : F) *
            matchingAvoidingInjectionSum p P b := by
              simpa [wp] using
                matching_leftWeightedAvoidingInjectionSum p P Q b
      _ = ((m - 1 - P.card).descFactorial Q.card : F) *
          (matchingPolynomial p P).eval (p b) := by
            rw [matchingPolynomial_eval]
  have hright :
      (∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}), wq theta) =
        ((m - 1 - Q.card).descFactorial P.card : F) *
          (matchingPolynomial q Q).eval (q a) := by
    calc
      (∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}), wq theta) =
          ((m - 1 - Q.card).descFactorial P.card : F) *
            matchingAvoidingInjectionSum q Q a := by
              simpa [wq] using
                matching_rightWeightedAvoidingInjectionSum q P Q a
      _ = ((m - 1 - Q.card).descFactorial P.card : F) *
          (matchingPolynomial q Q).eval (q a) := by
            rw [matchingPolynomial_eval]
  have hcross := sum_matchingCrossPermutation_rows_cols
    (F := F) (T := ↥P ⊕ ↥Q)
    (A := {j : Fin m // j ≠ a})
    (B := {j : Fin m // j ≠ b}) hcard
      (fun rho theta => wp rho * wq theta)
  calc
    (∑ σ : MatchingCrossPermutation (↥P ⊕ ↥Q)
      {j : Fin m // j ≠ a} {j : Fin m // j ≠ b},
        matchingCrossWeight p q P Q a b σ) =
      ((Fintype.card {j : Fin m // j ≠ a} -
        Fintype.card (↥P ⊕ ↥Q)).factorial : F) *
        (∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}),
          ∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}),
            wp rho * wq theta) := by
              simpa [matchingCrossWeight, wp, wq] using hcross
    _ = ((m - 1 - P.card - Q.card).factorial : F) *
        ((∑ rho : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ b}), wp rho) *
          (∑ theta : ((↥P ⊕ ↥Q) ↪ {j : Fin m // j ≠ a}),
            wq theta)) := by
              rw [hfact, hsplit]
    _ = (matchingJacobianWeight m P.card Q.card : F) *
        ((matchingPolynomial p P).eval (p b) *
          (matchingPolynomial q Q).eval (q a)) := by
            rw [hleft, hright]
            simp only [matchingJacobianWeight, Nat.cast_mul]
            ring
end PermanentFormulaLowerBound
