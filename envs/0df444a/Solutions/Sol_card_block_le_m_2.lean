-- Prove2me | solution 2 for card_block_le_m
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-23T08:58:02.085221+00:00
-- url     : https://prove2.me/submissions/12eb3130-7aa7-4a8b-95f5-a8aba00a1fff

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem card_block_le_m {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ) (z : F)
    (hm : m > 0) : (Block D m z).card ≤ m := by
  unfold Block
  calc (D.filter fun y => y ^ m = z).card ≤ (Polynomial.nthRoots m z).toFinset.card := by
        apply Finset.card_le_card
        intro y hy
        simp only [Finset.mem_filter] at hy
        simpa [Multiset.mem_toFinset, Polynomial.mem_nthRoots hm] using hy.2
    _ ≤ (Polynomial.nthRoots m z).card := Multiset.toFinset_card_le _
    _ ≤ m := Polynomial.card_nthRoots m z

theorem solution {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ) (z : F)
    (hm : m > 0) : (Block D m z).card ≤ m := by
  unfold Block
  calc (D.filter fun y => y ^ m = z).card ≤ (Polynomial.nthRoots m z).toFinset.card := by
        apply Finset.card_le_card
        intro y hy
        simp only [Finset.mem_filter] at hy
        simpa [Multiset.mem_toFinset, Polynomial.mem_nthRoots hm] using hy.2
    _ ≤ (Polynomial.nthRoots m z).card := Multiset.toFinset_card_le _
    _ ≤ m := Polynomial.card_nthRoots m z
