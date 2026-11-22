-- Prove2me | solution 1 for SZ.rec2_dvd_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:47:29.882875+00:00
-- url     : https://prove2.me/submissions/6593f126-4a61-4502-b4c0-d056920236a9

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
theorem _root_.solution {m A B t₀ t₁ : ℤ} (hA : m ∣ A) (hB : m ∣ (B - 1)) (n : ℕ) :
    m ∣ (rec2 A B t₀ t₁ n - if n % 2 = 0 then t₀ else t₁) := by
  induction n using SZ.twoStep with
  | h0 => simp
  | h1 => simp
  | hs n ih1 ih2 =>
    have key : rec2 A B t₀ t₁ (n + 2) - rec2 A B t₀ t₁ n
        = A * rec2 A B t₀ t₁ (n + 1) + (B - 1) * rec2 A B t₀ t₁ n := by
      rw [rec2_add_two]; ring
    have h2 : m ∣ (rec2 A B t₀ t₁ (n + 2) - rec2 A B t₀ t₁ n) := by
      rw [key]; exact dvd_add (hA.mul_right _) (hB.mul_right _)
    have hmod : (n + 2) % 2 = n % 2 := by omega
    rw [hmod]
    have e : rec2 A B t₀ t₁ (n + 2) - (if n % 2 = 0 then t₀ else t₁)
        = (rec2 A B t₀ t₁ (n + 2) - rec2 A B t₀ t₁ n)
          + (rec2 A B t₀ t₁ n - (if n % 2 = 0 then t₀ else t₁)) := by ring
    rw [e]
    exact dvd_add h2 ih1
end SZ
