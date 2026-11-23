-- Prove2me | solution 1 for P2M_segment__idem_e922dad3abb7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:52:28.257654+00:00
-- url     : https://prove2.me/submissions/63764251-7216-488f-923c-c5197a99d645

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
import Theorems.Thm_segment_idem
import Theorems.Thm_base_zero_strict_mono

set_option autoImplicit true
open Function Set
variable {φ : ℕ → ℕ}
theorem _root_.solution (hm : StrictMono φ) (k : ℕ) :
    Segment' φ (φ k) = k := by
  simp [Segment']
  exact segment_idem (base_zero_strict_mono hm) k
