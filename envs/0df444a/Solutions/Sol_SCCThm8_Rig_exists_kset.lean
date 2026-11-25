-- Prove2me | solution 1 for SCCThm8.Rig.exists_kset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:49:31.061802+00:00
-- url     : https://prove2.me/submissions/e4743bf2-02b8-49a5-b87c-8a0da94114be

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_card_compl_fin

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
namespace SCCThm8.Rig
theorem _root_.solution {k : ℕ} (s t : Finset (Fin n)) (hst : Disjoint s t) (hs : s.card ≤ k)
    (ht : k + t.card ≤ n) : ∃ A : Finset (Fin n), A.card = k ∧ s ⊆ A ∧ Disjoint A t := by
  obtain ⟨u, hsu, hut, hu⟩ := exists_subsuperset_card_eq (s := s) (t := tᶜ) (n := k)
    (by intro x hx; rw [mem_compl]; exact disjoint_left.mp hst hx) hs
    (by rw [card_compl_fin]; omega)
  exact ⟨u, hu, hsu, by rw [disjoint_left]; intro x hx; exact mem_compl.mp (hut hx)⟩
end SCCThm8.Rig
