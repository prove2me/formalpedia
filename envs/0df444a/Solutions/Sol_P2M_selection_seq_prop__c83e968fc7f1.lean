-- Prove2me | solution 1 for P2M_selection_seq_prop__c83e968fc7f1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:47:06.824803+00:00
-- url     : https://prove2.me/submissions/8eff1884-0dfc-4039-8feb-abc91e8b7de8

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic
import Definitions.Def_AutomataTheory_Mathlib_InfGraphRamsey

set_option autoImplicit true
open Function Set
open Classical
variable {Color Vertex : Type*} [Finite Color]
variable (color : (e : Edge) → Color)
variable [Infinite Vertex]
theorem _root_.solution (n : ℕ) :
    ∃ ivs : InfVSet Vertex, selection_prop color ivs (selection_seq color n) ∧
      (ivs.set = ⋂ m < n, (selection_seq color m).vs.set) := by
  induction' n with n h_ind
  . use (InfVSet.mk univ infinite_univ) ; simp
    exact choose_spec (selection_exists color (InfVSet.mk univ infinite_univ))
  obtain ⟨ivs, h_ivs, h_eq⟩ := h_ind
  use (selection_seq color n).vs ; constructor
  · exact choose_spec (selection_exists color (selection_seq color n).vs)
  · simp [(show ∀ m, m < n + 1 ↔ m < n ∨ m = n by omega),
      iInter_or, iInter_inter_distrib, iInter_iInter_eq_left, ← h_eq]
    exact h_ivs.1
