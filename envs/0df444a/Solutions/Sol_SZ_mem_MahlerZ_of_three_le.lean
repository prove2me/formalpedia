-- Prove2me | solution 1 for SZ.mem_MahlerZ_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:57:29.006399+00:00
-- url     : https://prove2.me/submissions/566384b9-5036-460f-a794-6b114c621db3

import Definitions.Def_SZ_Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_SZ_Tijdeman
import Theorems.Thm_SZ_greedy_zero
import Theorems.Thm_SZ_greedy_even
import Theorems.Thm_SZ_gLo_le_witness
import Theorems.Thm_SZ_floor_greedy
import Theorems.Thm_SZ_mem_MahlerZ_of_floor_eq

attribute [local simp] SZ.greedy_zero

set_option autoImplicit false
open SZ
variable {α : ℝ}
namespace SZ
theorem _root_.solution (hα : 3 ≤ α) : α ∈ MahlerZ := by
  have hpos : 0 < tijdemanWitness α := by
    refine lt_of_lt_of_le ?_ (gLo_le_witness hα 0)
    rw [gLo]; norm_num [greedy_zero]
  refine mem_MahlerZ_of_floor_eq (by linarith) (ne_of_gt hpos) 0 (greedy α)
    (fun n _ => greedy_even α n) (fun n _ => floor_greedy hα n)
end SZ
