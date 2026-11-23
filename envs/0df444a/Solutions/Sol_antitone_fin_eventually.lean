-- Prove2me | solution 1 for antitone_fin_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:32:01.259214+00:00
-- url     : https://prove2.me/submissions/b6e3e37d-5bf4-4864-b8a1-ecbc319e4bc1

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic

set_option autoImplicit true
open Function Set Option Stream'
theorem _root_.solution {n : ℕ} {f : ℕ → Fin n} (h : Antitone f) :
    ∃ i : Fin n, ∃ m, ∀ k ≥ m, f k = i := by
  have h_fin : (range f).Finite := toFinite (range f)
  have h_ne : (range f).Nonempty := by use (f 0) ; simp
  obtain ⟨i, ⟨m, rfl⟩, h_min⟩ := Finite.exists_minimal h_fin h_ne
  use (f m), m ; intro k h_k
  have h_k_m := h h_k
  have h_m_k := h_min (show f k ∈ range f by simp) h_k_m
  exact Fin.le_antisymm h_k_m h_m_k
