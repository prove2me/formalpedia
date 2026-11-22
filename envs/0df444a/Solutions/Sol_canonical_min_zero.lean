-- Prove2me | solution 1 for canonical_min_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:39:42.817729+00:00
-- url     : https://prove2.me/submissions/8bf9ec37-fbfd-4c1b-a845-4cdabfd1efba

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ

set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset
theorem _root_.solution {n : ℕ} (hn : n ≠ 0)
    (h : ∀ S : Finset ℤ, #S = n → Minimal (· ∈ S) 0 → HasPolychromColouring K S) :
    ∀ S : Finset ℤ, #S = n → HasPolychromColouring K S := by
  intro S hS
  obtain ⟨d, hd⟩ : ∃ i, Minimal (· ∈ S) i := by
    apply Finset.exists_minimal
    rw [← Finset.card_pos]
    simp [hS, pos_iff_ne_zero, hn]
  wlog hd₀ : d = 0 generalizing S d
  · suffices HasPolychromColouring K (-d +ᵥ S) by simpa
    apply this ((-d) +ᵥ S) (by simpa) 0 _ rfl
    simpa [Minimal, Finset.mem_vadd_finset, neg_add_eq_sub, sub_eq_zero] using hd
  cases hd₀
  exact h S hS hd
