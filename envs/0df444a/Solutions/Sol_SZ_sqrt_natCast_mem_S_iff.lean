-- Prove2me | solution 1 for SZ.sqrt_natCast_mem_S_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:52.085905+00:00
-- url     : https://prove2.me/submissions/3cd316d7-2078-4447-99a2-edf0fe7671ca

import Definitions.Def_SZ_SliceHygiene
import Definitions.Def_SZ_SqrtTwo
import Definitions.Def_SZ_SqrtThree
import Definitions.Def_SZ_Tijdeman
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_Cells
import Theorems.Thm_SZ_sqrt_natCast_mem_MahlerZ
import Theorems.Thm_SZ_greedy_zero
import Theorems.Thm_SZ_sqrtTwo_mem_S
attribute [local simp] SZ.greedy_zero



set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) : Real.sqrt m ∈ S ↔ m = 2 := by
  constructor
  · intro hS
    by_contra hne
    exact hS.2 (sqrt_natCast_mem_MahlerZ hm hne)
  · rintro rfl
    simpa using sqrtTwo_mem_S
end SZ
