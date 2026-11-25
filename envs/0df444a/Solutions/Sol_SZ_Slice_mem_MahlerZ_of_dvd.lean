-- Prove2me | solution 1 for SZ.Slice.mem_MahlerZ_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:18:50.625219+00:00
-- url     : https://prove2.me/submissions/8285ad98-957b-4dec-80c0-6433467746ff

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_one_lt_sq

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}
namespace SZ.Slice
theorem _root_.solution (S : Slice) (hp : S.p = 2)
    (h : ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → S.p ∣ ⌊ξ * Real.sqrt S.m ^ n⌋) :
    Real.sqrt S.m ∈ MahlerZ := by
  obtain ⟨ξ, hξ, hdvd⟩ := h
  refine ⟨S.one_lt_sq, ξ, ne_of_gt hξ, fun n hn => ?_⟩
  have := hdvd n hn
  rw [hp] at this
  exact even_iff_two_dvd.mpr this
end SZ.Slice
