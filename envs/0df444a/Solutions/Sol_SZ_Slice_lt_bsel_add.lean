-- Prove2me | solution 1 for SZ.Slice.lt_bsel_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:45:16.839799+00:00
-- url     : https://prove2.me/submissions/93aa4bc9-ca6a-42b1-bf60-860eaa48aa1a

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
import Theorems.Thm_SZ_Slice_p_sq_pos

set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)
namespace SZ.Slice
theorem _root_.solution {w : ℝ} (h : S.bsel w < S.e) :
    w < ((S.bsel w : ℝ) + (S.p : ℝ)) * S.sq := by
  have hs : (0 : ℝ) < (S.p : ℝ) * S.sq := S.p_sq_pos
  have hb : S.bsel w = S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋ := by
    rcases min_cases S.e (S.p * ⌊w / ((S.p : ℝ) * S.sq)⌋) with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [bsel, h1] at h; omega
    · rw [bsel, h1]
  have hf : w / ((S.p : ℝ) * S.sq) < (⌊w / ((S.p : ℝ) * S.sq)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hw := (div_lt_iff₀ hs).mp hf
  have hid : ((⌊w / ((S.p : ℝ) * S.sq)⌋ : ℝ) + 1) * ((S.p : ℝ) * S.sq)
      = ((S.p : ℝ) * (⌊w / ((S.p : ℝ) * S.sq)⌋ : ℝ) + (S.p : ℝ)) * S.sq := by ring
  rw [hb]
  push_cast
  linarith [hid ▸ hw]
end SZ.Slice
