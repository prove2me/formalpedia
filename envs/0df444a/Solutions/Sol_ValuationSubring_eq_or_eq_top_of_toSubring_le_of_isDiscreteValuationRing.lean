-- Prove2me | solution 1 for ValuationSubring.eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f2ca8bde-485a-5f3a-bbe1-48733358736b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing

set_option autoImplicit false

theorem solution
    {K : Type} [Field K] (A : ValuationSubring K) [IsDiscreteValuationRing ↥A]
    (B : Subring K) (h : A.toSubring ≤ B) : B = A.toSubring ∨ B = ⊤ := by
  classical
  let B' : ValuationSubring K := ValuationSubring.ofLE A B h
  have hB' : (B' : ValuationSubring K).toSubring = B := rfl
  have hAB' : A ≤ B' := fun x hx => h hx

  set P : Ideal ↥A := A.idealOfLE B' hAB' with hP
  have hPB' : A.ofPrime P = B' := ValuationSubring.ofPrime_idealOfLE A B' hAB'
  by_cases hbot : P = ⊥
  · right
    rw [← hB', ← hPB']
    have : A.ofPrime P = ⊤ := by
      haveI : (⊥ : Ideal ↥A).IsPrime := Ideal.bot_prime
      have e : A.ofPrime P = A.ofPrime ⊥ := by congr 1
      rw [e]; exact ValuationSubring.ofPrime_bot A
    rw [this]; rfl
  · left
    rw [← hB', ← hPB']
    have hmax : P.IsMaximal := IsPrime.to_maximal_ideal hbot
    have hPm : P = IsLocalRing.maximalIdeal ↥A := IsLocalRing.eq_maximalIdeal hmax
    have : A.ofPrime P = A := by
      have e : A.ofPrime P = A.ofPrime (IsLocalRing.maximalIdeal ↥A) := by congr 1
      rw [e]; exact ValuationSubring.ofPrime_top A
    rw [this]

end S_ValuationSubring_eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing
end P2MW
export P2MW.S_ValuationSubring_eq_or_eq_top_of_toSubring_le_of_isDiscreteValuationRing (solution)
