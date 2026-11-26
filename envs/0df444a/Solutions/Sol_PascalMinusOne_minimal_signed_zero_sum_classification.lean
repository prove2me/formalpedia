-- Prove2me | solution 1 for PascalMinusOne.minimal_signed_zero_sum_classification
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:20.699171+00:00
-- url     : https://prove2.me/submissions/e19b9ad6-ed8c-4a0b-9b68-dbf5a52056fc

import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Definitions.Def_PascalMinusOne_SignedTokens
import Theorems.Thm_PascalMinusOne_signedZeroSum_one_one
import Theorems.Thm_PascalMinusOne_signedZeroSum_m_zero
import Theorems.Thm_PascalMinusOne_signedZeroSum_zero_m
import Theorems.Thm_PascalMinusOne_signedZeroSum_right_zero_iff
import Theorems.Thm_PascalMinusOne_signedZeroSum_zero_left_iff
attribute [local simp] PascalMinusOne.signedZeroSum_one_one
attribute [local simp] PascalMinusOne.signedZeroSum_m_zero
attribute [local simp] PascalMinusOne.signedZeroSum_zero_m

set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution {m A B : ℕ} (hm : 3 ≤ m) :
    MinimalSignedZeroSum m A B ↔
      (A = 1 ∧ B = 1) ∨ (A = m ∧ B = 0) ∨ (A = 0 ∧ B = m) := by
  constructor
  · rintro ⟨hpos, hzero, hminimal⟩
    by_cases hA : A = 0
    · subst A
      have hBpos : 0 < B := by omega
      have hmB : m ∣ B := (signedZeroSum_zero_left_iff m B).1 hzero
      have hmleB : m ≤ B := Nat.le_of_dvd hBpos hmB
      have hBle : B ≤ m := by
        by_contra h
        have hmBlt : m < B := by omega
        apply hminimal
        refine ⟨0, m, by simp, hmleB, ?_, ?_, signedZeroSum_zero_m m⟩
        · omega
        · omega
      exact Or.inr (Or.inr ⟨rfl, Nat.le_antisymm hBle hmleB⟩)
    · have hApos : 0 < A := Nat.pos_of_ne_zero hA
      by_cases hB : B = 0
      · subst B
        have hmA : m ∣ A := (signedZeroSum_right_zero_iff m A).1 hzero
        have hmleA : m ≤ A := Nat.le_of_dvd hApos hmA
        have hAle : A ≤ m := by
          by_contra h
          have hmAlt : m < A := by omega
          apply hminimal
          refine ⟨m, 0, hmleA, by simp, ?_, ?_, signedZeroSum_m_zero m⟩
          · omega
          · omega
        exact Or.inr (Or.inl ⟨Nat.le_antisymm hAle hmleA, rfl⟩)
      · have hBpos : 0 < B := Nat.pos_of_ne_zero hB
        have hsum_le : A + B ≤ 2 := by
          by_contra h
          have htwo_lt : 2 < A + B := by omega
          apply hminimal
          refine ⟨1, 1, ?_, ?_, ?_, ?_, signedZeroSum_one_one m⟩ <;> omega
        exact Or.inl ⟨by omega, by omega⟩
  · rintro (h11 | hm0 | h0m)
    · rcases h11 with ⟨rfl, rfl⟩
      refine ⟨by omega, signedZeroSum_one_one m, ?_⟩
      rintro ⟨a, b, ha, hb, hpos, hproper, hzero⟩
      have hab :
          (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
        omega
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hdiv : m ∣ 1 := (signedZeroSum_right_zero_iff m 1).1 hzero
        have hm1 : m = 1 := Nat.dvd_one.mp hdiv
        omega
      · have hdiv : m ∣ 1 := (signedZeroSum_zero_left_iff m 1).1 hzero
        have hm1 : m = 1 := Nat.dvd_one.mp hdiv
        omega
    · rcases hm0 with ⟨hA, hB⟩
      subst A
      subst B
      refine ⟨by omega, signedZeroSum_m_zero m, ?_⟩
      rintro ⟨a, b, ha, hb, hpos, hproper, hzero⟩
      have hb0 : b = 0 := by omega
      subst b
      have hapos : 0 < a := by omega
      have hdiv : m ∣ a := (signedZeroSum_right_zero_iff m a).1 hzero
      have hma : m ≤ a := Nat.le_of_dvd hapos hdiv
      omega
    · rcases h0m with ⟨hA, hB⟩
      subst A
      subst B
      refine ⟨by omega, signedZeroSum_zero_m m, ?_⟩
      rintro ⟨a, b, ha, hb, hpos, hproper, hzero⟩
      have ha0 : a = 0 := by omega
      subst a
      have hbpos : 0 < b := by omega
      have hdiv : m ∣ b := (signedZeroSum_zero_left_iff m b).1 hzero
      have hmb : m ≤ b := Nat.le_of_dvd hbpos hdiv
      omega
end PascalMinusOne
