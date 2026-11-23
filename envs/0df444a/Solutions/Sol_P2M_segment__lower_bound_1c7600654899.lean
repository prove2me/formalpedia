-- Prove2me | solution 1 for P2M_segment__lower_bound_1c7600654899
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:33:33.237824+00:00
-- url     : https://prove2.me/submissions/241a18a2-3268-42a0-9e1a-6114343e9e94

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_segment_lower_bound
import Theorems.Thm_base_zero_shift
import Theorems.Thm_base_zero_strict_mono

set_option autoImplicit true
open Function Set
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) {k : ℕ} (h : φ 0 ≤ k) :
    φ (Segment' φ k) ≤ k := by
  simp [Segment']
  have := segment_lower_bound (base_zero_strict_mono hm) (base_zero_shift φ) (k - φ 0)
  omega
