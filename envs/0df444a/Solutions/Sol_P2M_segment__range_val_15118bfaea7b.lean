-- Prove2me | solution 1 for P2M_segment__range_val_15118bfaea7b
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:52:57.654812+00:00
-- url     : https://prove2.me/submissions/5dfa4640-4716-46fe-a3c2-75bc8d21a03d

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_segment_range_val
import Theorems.Thm_base_zero_strict_mono

set_option autoImplicit true
open Function Set
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m ≤ k) (hu : k < φ (m + 1)) : Segment' φ k = m := by
  simp [Segment']
  have h : φ 0 ≤ k := by
    have : φ 0 ≤ φ m := by simp [StrictMono.le_iff_le hm]
    omega
  have hl' : (φ · - φ 0) m ≤ k - φ 0 := by simp ; omega
  have hu' : k - φ 0 < (φ · - φ 0) (m + 1) := by simp ; omega
  exact segment_range_val (base_zero_strict_mono hm) hl' hu'
