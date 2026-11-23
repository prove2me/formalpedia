-- Prove2me | solution 1 for P2M_segment__zero_b18716f7ae0d
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:52:25.176207+00:00
-- url     : https://prove2.me/submissions/5a94b791-e259-4ed0-8e51-00deb858d821

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_segment_zero
import Theorems.Thm_base_zero_shift
import Theorems.Thm_base_zero_strict_mono

set_option autoImplicit true
open Function Set
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) {k : ℕ} (h : k ≤ φ 0) :
    Segment' φ k = 0 := by
  simp [Segment', (show k - φ 0 = 0 by omega)]
  exact segment_zero (base_zero_strict_mono hm) (base_zero_shift φ)
