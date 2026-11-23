-- Prove2me | solution 1 for base_zero_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:13:39.518691+00:00
-- url     : https://prove2.me/submissions/67fc1ea6-3ae8-4556-905b-aa52fed74342

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments

set_option autoImplicit true
open Function Set
theorem _root_.solution (φ : ℕ → ℕ) :
    (φ · - φ 0) 0 = 0 := by
  simp
