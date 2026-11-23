-- Prove2me | solution 1 for card_block_le_m
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:57:06.208544+00:00
-- url     : https://prove2.me/submissions/1301b050-23e4-493a-9f3a-2d6784a395c9

import Mathlib
import Definitions.Def_SimpleRbrFri_Core

set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F] (D : Finset F) (m : ℕ) (z : F)
    (hm : m > 0) : (Block D m z).card ≤ m := by
  have h_roots : (Block D m z).card ≤
      (Polynomial.roots (Polynomial.X ^ m - Polynomial.C z)).toFinset.card := by
    refine Finset.card_le_card ?_
    intro x hx
    simp_all only [gt_iff_lt, Block, Finset.mem_filter, Multiset.mem_toFinset,
      mem_roots', ne_eq, IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_self, and_true]
    exact Polynomial.X_pow_sub_C_ne_zero hm z
  exact h_roots.trans <| (Multiset.toFinset_card_le _).trans <|
    Polynomial.card_roots_X_pow_sub_C hm z
