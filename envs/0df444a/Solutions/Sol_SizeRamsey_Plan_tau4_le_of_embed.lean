-- Prove2me | solution 1 for SizeRamsey.Plan.tau4_le_of_embed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:24.485916+00:00
-- url     : https://prove2.me/submissions/bfe5f39a-da3d-4ed5-9809-ecabbbcbd5d6

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_exists_transversal_card_eq_tau4
public import Theorems.Thm_SizeRamsey_tau4_le_card


set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} {W : Type*}
namespace SizeRamsey.Plan
theorem _root_.solution [Fintype V] [Fintype W] {G : SimpleGraph V} {H : SimpleGraph W}
    (g : W → V)
    (hsq : ∀ f, IsC4Map G f → ∃ f', IsC4Map H f' ∧ g ∘ f' = f) : tau4 G ≤ tau4 H := by
  obtain ⟨T, hT, hcard⟩ := exists_transversal_card_eq_tau4 H
  have hS : c4Transversal G (T.image g) := by
    intro f hf
    obtain ⟨f', hf', rfl⟩ := hsq f hf
    obtain ⟨i, hi⟩ := hT _ hf'
    exact ⟨i, Finset.mem_image_of_mem g hi⟩
  exact (tau4_le_card hS).trans (hcard ▸ Finset.card_image_le)
end SizeRamsey.Plan
