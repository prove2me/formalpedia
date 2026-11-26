-- Prove2me | solution 1 for TunnellMap.natSqrtK_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:42.262021+00:00
-- url     : https://prove2.me/submissions/92ca3e66-beed-48a4-9e03-5b2c67ab5e82

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
import Theorems.Thm_TunnellMap_natSqrtK_spec

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (n : ℕ) : natSqrtK n = Nat.sqrt n := by
  obtain ⟨h₁, h₂⟩ := natSqrtK_spec n
  have hle : natSqrtK n ≤ Nat.sqrt n := Nat.le_sqrt.mpr h₁
  have hlt : Nat.sqrt n < natSqrtK n + 1 := Nat.sqrt_lt.mpr h₂
  omega
end TunnellMap
