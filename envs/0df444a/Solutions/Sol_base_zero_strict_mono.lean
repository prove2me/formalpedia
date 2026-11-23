-- Prove2me | solution 1 for base_zero_strict_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:11:52.563653+00:00
-- url     : https://prove2.me/submissions/b5fbcecf-2b8b-4fba-9395-8f14599bfb22

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments

set_option autoImplicit true
open Function Set
theorem _root_.solution {φ : ℕ → ℕ} (hm : StrictMono φ) :
    StrictMono (φ · - φ 0) := by
  intro m n h_m_n ; simp
  have := hm h_m_n
  have : φ 0 ≤ φ m := by simp [StrictMono.le_iff_le hm]
  have : φ 0 ≤ φ n := by simp [StrictMono.le_iff_le hm]
  omega
