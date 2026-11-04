-- Prove2me | solution 1 for ThreeSum.TernaryPairedBudgetSelector.exists_budget_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:24:34.007936+00:00
-- url     : https://prove2.me/submissions/d676d8f9-2c20-4e17-adc1-f2b02937a1ac

import Definitions.Def_Submission_ThreeSum_TernaryPairedSelector
import Definitions.Def_Submission_ThreeSum_TernaryPairedRecurrence
import Definitions.Def_Submission_ThreeSum_TernaryPairedBudgetSelector
import Theorems.Thm_ThreeSum_TernaryPairedSelector_exists_cross_multiplied


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedBudgetSelector
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
namespace ThreeSum.TernaryPairedBudgetSelector
theorem _root_.solution {Ω : Type*} [DecidableEq Ω]
    (S : Finset Ω) (hS : S.Nonempty) (a c p s j U N curPi curB curC : ℕ)
    (ha : 0<a) (hp : 0<p) (nextPi nextB nextC : Ω→ℕ)
    (hPi : a*(∑ x∈S,nextPi x)≤3*S.card*c*curPi)
    (hB : p*(∑ x∈S,nextB x)≤3*S.card*curB)
    (hC : p*(∑ x∈S,nextC x)≤3*S.card*curC)
    (hPiBudget : a^j*curPi≤(9*c)^j*U)
    (hBBudget : p^j*curB≤9^j*N) (hCBudget : p^j*curC≤9^j*N) :
    ∃ x∈S,
      a^(j+1)*(s*nextPi x)≤s*(9*c)^(j+1)*U ∧
      p^(j+1)*nextB x≤9^(j+1)*N ∧ p^(j+1)*nextC x≤9^(j+1)*N := by
  let f : Fin 3→Ω→ℕ := ![fun x => s*nextPi x,nextB,nextC]
  let num : Fin 3→ℕ := ![s*c*(9*c)^j*U,9^j*N,9^j*N]
  let den : Fin 3→ℕ := ![a^(j+1),p^(j+1),p^(j+1)]
  have hPi' : den 0*(∑ x∈S,f 0 x)≤3*S.card*num 0 := by
    change a^(j+1)*(∑ x∈S,s*nextPi x)≤3*S.card*(s*c*(9*c)^j*U)
    rw [←mul_sum]
    calc
      _ = s*a^j*(a*(∑ x∈S,nextPi x)) := by rw [pow_succ]; ring
      _ ≤ s*a^j*(3*S.card*c*curPi) := Nat.mul_le_mul_left _ hPi
      _ = (3*S.card*s*c)*(a^j*curPi) := by ring
      _ ≤ (3*S.card*s*c)*((9*c)^j*U) := Nat.mul_le_mul_left _ hPiBudget
      _ = _ := by ring
  have hB' : den 1*(∑ x∈S,f 1 x)≤3*S.card*num 1 := by
    change p^(j+1)*(∑ x∈S,nextB x)≤3*S.card*(9^j*N)
    calc
      _ = p^j*(p*(∑ x∈S,nextB x)) := by rw [pow_succ]; ring
      _ ≤ p^j*(3*S.card*curB) := Nat.mul_le_mul_left _ hB
      _ = (3*S.card)*(p^j*curB) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hBBudget
  have hC' : den 2*(∑ x∈S,f 2 x)≤3*S.card*num 2 := by
    change p^(j+1)*(∑ x∈S,nextC x)≤3*S.card*(9^j*N)
    calc
      _ = p^j*(p*(∑ x∈S,nextC x)) := by rw [pow_succ]; ring
      _ ≤ p^j*(3*S.card*curC) := Nat.mul_le_mul_left _ hC
      _ = (3*S.card)*(p^j*curC) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hCBudget
  obtain ⟨x,hx,hs⟩ := TernaryPairedSelector.exists_cross_multiplied S hS f num den
    (by intro i; fin_cases i <;> dsimp [den] <;> positivity)
    (by intro i; fin_cases i; exact hPi'; exact hB'; exact hC')
  refine ⟨x,hx,?_,?_,?_⟩
  · calc
      _ ≤ 9*(s*c*(9*c)^j*U) := hs 0
      _ = _ := by rw [pow_succ]; ring
  · calc
      _ ≤ 9*(9^j*N) := hs 1
      _ = _ := by rw [pow_succ]; ring
  · calc
      _ ≤ 9*(9^j*N) := hs 2
      _ = _ := by rw [pow_succ]; ring
end ThreeSum.TernaryPairedBudgetSelector
