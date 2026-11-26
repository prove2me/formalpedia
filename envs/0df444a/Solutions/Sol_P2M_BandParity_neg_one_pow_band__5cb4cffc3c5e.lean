-- Prove2me | solution 1 for P2M_BandParity_neg_one_pow_band__5cb4cffc3c5e
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:02:25.559889+00:00
-- url     : https://prove2.me/submissions/8224a731-12d4-4244-8e9e-b5e2f9969eb5

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp2 : p ≠ 2) (x : ZMod p) :
    (-1 : ℤ) ^ band x = parSign x * parSign (x ^ 2) := by
  unfold parSign band
  have hsq : (x ^ 2).val = x.val ^ 2 % p := by rw [sq, ZMod.val_mul, sq]
  rw [hsq]
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have h1 : (-1 : ℤ) ^ (x.val ^ 2) = (-1) ^ x.val := by
    rcases Nat.even_or_odd x.val with h | h
    · rw [h.neg_one_pow, (Nat.even_pow.2 ⟨h, two_ne_zero⟩).neg_one_pow]
    · rw [h.neg_one_pow, (h.pow).neg_one_pow]
  have h2 : (-1 : ℤ) ^ (x.val ^ 2) =
      (-1) ^ (x.val ^ 2 / p) * (-1) ^ (x.val ^ 2 % p) := by
    conv_lhs => rw [← Nat.div_add_mod (x.val ^ 2) p]
    rw [pow_add, pow_mul, hpodd.neg_one_pow]
  have hr : (-1 : ℤ) ^ (x.val ^ 2 % p) * (-1) ^ (x.val ^ 2 % p) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have E := h1.symm.trans h2
  linear_combination (-((-1 : ℤ) ^ (x.val ^ 2 % p))) * E + (-((-1 : ℤ) ^ (x.val ^ 2 / p))) * hr
end BandParity
