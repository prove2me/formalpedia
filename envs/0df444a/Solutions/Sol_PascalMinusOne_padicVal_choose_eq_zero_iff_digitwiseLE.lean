-- Prove2me | solution 1 for PascalMinusOne.padicVal_choose_eq_zero_iff_digitwiseLE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:38.697729+00:00
-- url     : https://prove2.me/submissions/e5fac3b6-7d3f-4cca-a3c3-803112abcff7

import Definitions.Def_PascalMinusOne_Basic
import Definitions.Def_PascalMinusOne_Digits
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_PascalMinusOne_Kummer
import Theorems.Thm_PascalMinusOne_padicVal_choose_eq_carryCount
import Theorems.Thm_PascalMinusOne_digitwiseLE_iff_mod_pow_le
import Theorems.Thm_PascalMinusOne_not_carryAt_iff_mod_pow_le
import Theorems.Thm_PascalMinusOne_evenDigitSum_zero
import Theorems.Thm_PascalMinusOne_mem_admissibleIndices_iff
import Theorems.Thm_PascalMinusOne_oddDigitSum_zero
import Theorems.Thm_PascalMinusOne_parityDigitSums_cons
import Theorems.Thm_PascalMinusOne_parityDigitSums_nil
attribute [local simp] PascalMinusOne.evenDigitSum_zero
attribute [local simp] PascalMinusOne.mem_admissibleIndices_iff
attribute [local simp] PascalMinusOne.oddDigitSum_zero
attribute [local simp] PascalMinusOne.parityDigitSums_cons
attribute [local simp] PascalMinusOne.parityDigitSums_nil



set_option autoImplicit true
open PascalMinusOne
namespace PascalMinusOne
theorem _root_.solution {p n k : ℕ} [Fact p.Prime]
    (hkn : k ≤ n) :
    padicValNat p (n.choose k) = 0 ↔ DigitwiseLE p k n := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  constructor
  · intro hval
    rw [digitwiseLE_iff_mod_pow_le hp]
    intro i
    cases i with
    | zero =>
        simpa only [pow_zero, Nat.mod_one] using (Nat.le_refl 0)
    | succ i =>
        let b := max (Nat.log p n + 1) (i + 2)
        have hnb : Nat.log p n < b := by
          dsimp [b]
          exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
        have hcount : carryCount p n k b = 0 := by
          rw [← padicVal_choose_eq_carryCount hkn hnb]
          exact hval
        have hall : ∀ j ∈ Finset.Ico 1 b, ¬ CarryAt p n k j := by
          exact Finset.card_filter_eq_zero_iff.mp (by
            simpa [carryCount] using hcount)
        have hib : i + 1 < b := by
          dsimp [b]
          exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
        have hnocarry : ¬ CarryAt p n k (i + 1) :=
          hall (i + 1) (by
            simp only [Finset.mem_Ico]
            exact ⟨Nat.succ_le_succ (Nat.zero_le _), hib⟩)
        exact
          (not_carryAt_iff_mod_pow_le (p := p) (n := n) (k := k) (i := i + 1) hp hkn).1
            hnocarry
  · intro hdigit
    have hprefix :
        ∀ i, k % p ^ i ≤ n % p ^ i :=
      (digitwiseLE_iff_mod_pow_le (p := p) (k := k) (n := n) hp).1 hdigit
    let b := Nat.log p n + 1
    have hnb : Nat.log p n < b := by
      dsimp [b]
      exact Nat.lt_succ_self _
    rw [padicVal_choose_eq_carryCount hkn hnb, carryCount,
      Finset.card_filter_eq_zero_iff]
    intro i hi
    exact
      (not_carryAt_iff_mod_pow_le (p := p) (n := n) (k := k) (i := i) hp hkn).2
        (hprefix i)
end PascalMinusOne
