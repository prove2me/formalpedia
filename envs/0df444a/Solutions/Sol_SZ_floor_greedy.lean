-- Prove2me | solution 1 for SZ.floor_greedy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:56:54.283774+00:00
-- url     : https://prove2.me/submissions/bd41b7fe-0004-48f0-a133-4e7dfb978c39

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
import Theorems.Thm_SZ_gLo_le_witness
import Theorems.Thm_SZ_witness_lt_gHi

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (hα : 3 ≤ α) (n : ℕ) :
    ⌊tijdemanWitness α * α ^ n⌋ = greedy α n := by
  have hα0 : (0 : ℝ) < α := by linarith
  have hp : (0 : ℝ) < α ^ n := pow_pos hα0 n
  have h1 := gLo_le_witness hα n
  have h2 := witness_lt_gHi hα n
  rw [gLo, div_le_iff₀ hp] at h1
  rw [gHi, lt_div_iff₀ hp] at h2
  rw [Int.floor_eq_iff]
  exact ⟨by linarith, by linarith⟩
end SZ
