-- Prove2me | solution 1 for RamanujanNested.altSum_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-27T05:02:20.936809+00:00
-- url     : https://prove2.me/submissions/327ce0b0-500d-438f-a08e-3fea14413c83

module
public import Mathlib
public import Definitions.Def_RamanujanNested_IdentityChainNthRoot

set_option autoImplicit true
@[expose] public section
open RamanujanNested
open Finset
namespace RamanujanNested
theorem _root_.solution (n : ℕ) (x : ℝ) :
    altSum n x * (x + 1) = x ^ n - (-1 : ℝ) ^ n := by
  unfold altSum
  have h := geom_sum₂_mul x (-1 : ℝ) n
  rwa [sub_neg_eq_add] at h
end RamanujanNested
