-- Prove2me | solution 1 for P2M_segment__lower_val_a0fd010b0c15
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:35:43.292438+00:00
-- url     : https://prove2.me/submissions/f2557c9d-b9f2-4735-a0fd-5232012af72a

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_segment_galois_connection
import Theorems.Thm_base_zero_shift
import Theorems.Thm_base_zero_strict_mono

set_option autoImplicit true
open Function Set
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m ≤ k) : m ≤ Segment' φ k := by
  simp [Segment']
  have : φ 0 ≤ φ m := by simp [StrictMono.le_iff_le hm]
  exact (segment_galois_connection (base_zero_strict_mono hm) (base_zero_shift φ) m (k - φ 0)).mp (by omega)
