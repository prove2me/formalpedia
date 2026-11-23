-- Prove2me | solution 1 for P2M_segment__upper_bound_c7d48b2c3975
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:35:00.481797+00:00
-- url     : https://prove2.me/submissions/42853e5a-46b6-4c00-83be-eddf22458ef9

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_segment_upper_bound
import Theorems.Thm_base_zero_shift
import Theorems.Thm_base_zero_strict_mono

set_option autoImplicit true
open Function Set
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) {k : ℕ} (h : φ 0 ≤ k) :
    k < φ (Segment' φ k + 1) := by
  simp [Segment']
  have := segment_upper_bound (base_zero_strict_mono hm) (base_zero_shift φ) (k - φ 0)
  omega
