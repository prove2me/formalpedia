-- Prove2me | solution 1 for SZ.Slice.dvd_floor_of_e_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:57:44.878029+00:00
-- url     : https://prove2.me/submissions/0b7f347b-684b-4554-9b5f-3a8c2c2e4a3f

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_three_le_cast
import Theorems.Thm_SZ_Slice_dA_mem
import Theorems.Thm_SZ_Slice_dB_mem
import Theorems.Thm_SZ_Slice_dvd_floor_of_hygiene

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
variable {S}
namespace SZ.Slice
theorem _root_.solution (S : Slice) (he : S.e ≤ (S.m : ℤ) - 2) {j k₀ : ℤ} (hj : 1 ≤ j)
    (h0 : 0 ≤ S.sigma j k₀) (h1 : S.sigma j k₀ ≤ S.U) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → S.p ∣ ⌊ξ * Real.sqrt S.m ^ n⌋ := by
  have hm : (0 : ℝ) < (S.m : ℝ) := by have := S.three_le_cast; linarith
  have hw0 : 0 ≤ S.w0 j k₀ := mul_nonneg hm.le h0
  have hw1 : S.w0 j k₀ ≤ (S.m : ℝ) * S.U := mul_le_mul_of_nonneg_left h1 hm.le
  refine dvd_floor_of_hygiene S hj h0 h1 (fun N => ⟨N, le_refl N, ?_⟩)
    (fun N => ⟨N, le_refl N, ?_⟩)
  · exact le_trans (dA_mem hw0 hw1 N).2.2 he
  · have := (dB_mem hw0 hw1 N).2.1
    omega
end SZ.Slice
