-- Prove2me | solution 1 for TitiusBode.recursive_form
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T19:32:31.974995+00:00
-- url     : https://prove2.me/submissions/3a995af6-e569-460c-a8ae-bee696d30557

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology
open TitiusBode

theorem solution :
    (∀ n : ℕ, tbCanonical (n + 1) = 2 * tbCanonical n - 0.4) ∧
    (∀ n : ℕ, tbRecursive (n + 1) = tbCanonical n) ∧
    tbRecursive 0 ≠ tbCanonical 0 := by
  have hcan : ∀ n : ℕ, tbCanonical (n + 1) = 2 * tbCanonical n - 0.4 := by
    intro n
    simp only [tbCanonical, pow_succ]
    ring
  refine ⟨hcan, ?_, ?_⟩
  · intro n
    induction n with
    | zero => norm_num [tbRecursive, tbCanonical]
    | succ k ih => rw [tbRecursive, ih, hcan]
  · norm_num [tbRecursive, tbCanonical]
