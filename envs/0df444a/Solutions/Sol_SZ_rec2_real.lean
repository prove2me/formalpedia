-- Prove2me | solution 1 for SZ.rec2_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:44:53.542849+00:00
-- url     : https://prove2.me/submissions/cdc8ee25-a053-4c08-b2ba-4d7b9a01601f

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
theorem _root_.solution {A B t₀ t₁ : ℤ} {α β u v : ℝ}
    (hα : α ^ 2 = A * α + B) (hβ : β ^ 2 = A * β + B)
    (h0 : u + v = (t₀ : ℝ)) (h1 : u * α + v * β = (t₁ : ℝ)) (n : ℕ) :
    u * α ^ n + v * β ^ n = (rec2 A B t₀ t₁ n : ℝ) := by
  induction n using SZ.twoStep with
  | h0 => simpa using h0
  | h1 => simpa using h1
  | hs n ih1 ih2 =>
    have eα : α ^ (n + 2) = A * α ^ (n + 1) + B * α ^ n := by
      have e : α ^ (n + 2) = α ^ n * α ^ 2 := by ring
      rw [e, hα]; ring
    have eβ : β ^ (n + 2) = A * β ^ (n + 1) + B * β ^ n := by
      have e : β ^ (n + 2) = β ^ n * β ^ 2 := by ring
      rw [e, hβ]; ring
    rw [eα, eβ, rec2_add_two]
    push_cast
    linear_combination (A : ℝ) * ih2 + (B : ℝ) * ih1
end SZ
