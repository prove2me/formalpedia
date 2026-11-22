-- Prove2me | solution 1 for SZ.rec2_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:52:18.413414+00:00
-- url     : https://prove2.me/submissions/ba021cc1-b127-4b21-9c25-1bf281573efb

import Definitions.Def_SZ_Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Trace
import Theorems.Thm_SZ_twoStep
import Theorems.Thm_SZ_rec2_zero
import Theorems.Thm_SZ_rec2_one
import Theorems.Thm_SZ_rec2_add_two
attribute [local simp] SZ.rec2_zero
attribute [local simp] SZ.rec2_one

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution {A B t₀ t₁ : ℤ} (h0 : Even t₀) (h1 : Even t₁) (n : ℕ) :
    Even (rec2 A B t₀ t₁ n) := by
  induction n using SZ.twoStep with
  | h0 => simpa using h0
  | h1 => simpa using h1
  | hs n ih1 ih2 =>
    rw [rec2_add_two]
    exact (ih2.mul_left A).add (ih1.mul_left B)
end SZ
