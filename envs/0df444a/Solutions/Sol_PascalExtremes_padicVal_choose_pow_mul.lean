-- Prove2me | solution 1 for PascalExtremes.padicVal_choose_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:56:44.371527+00:00
-- url     : https://prove2.me/submissions/ab1ed13e-61f2-490c-b9c4-63b4946fce43

module
public import Definitions.Def_PascalExtremes_Basic
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Definitions.Def_PascalExtremes_Scaling
public import Theorems.Thm_PascalExtremes_mem_admissibleIndices_iff
attribute [local simp] PascalExtremes.mem_admissibleIndices_iff


section
@[expose] public section
namespace PascalExtremes
private theorem digitSum_pow_mul
    {p c n : ℕ} (hp : p.Prime) :
    (Nat.digits p (p ^ c * n)).sum = (Nat.digits p n).sum := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [Nat.digits_base_pow_mul hp.one_lt (Nat.pos_of_ne_zero hn), List.sum_append]
    simp
end PascalExtremes
end
end

set_option autoImplicit true
@[expose] public section
public section
open PascalExtremes
namespace PascalExtremes
theorem _root_.solution
    {p c n k : ℕ} (hp : p.Prime) (hkn : k ≤ n) :
    padicValNat p ((p ^ c * n).choose (p ^ c * k)) =
      padicValNat p (n.choose k) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hscaled : p ^ c * k ≤ p ^ c * n := Nat.mul_le_mul_left _ hkn
  have hs :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p) hscaled
  have hu :=
    sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p) hkn
  rw [← Nat.mul_sub_left_distrib,
    digitSum_pow_mul hp, digitSum_pow_mul hp, digitSum_pow_mul hp] at hs
  apply Nat.mul_left_cancel (Nat.sub_pos_of_lt hp.one_lt)
  exact hs.trans hu.symm
end PascalExtremes
