-- Prove2me | solution 1 for SizeRamsey.Plan.tau4_le_of_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:19:25.27842+00:00
-- url     : https://prove2.me/submissions/162e8e65-0978-4319-bd00-ff19a4478eaa

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
    (g : V → W) (hg : Function.Injective g)
    (hsq : ∀ f, IsC4Map G f → IsC4Map H (g ∘ f)) : tau4 G ≤ tau4 H := by
  obtain ⟨T, hT, hcard⟩ := exists_transversal_card_eq_tau4 H
  have hS : c4Transversal G (Finset.univ.filter (fun v => g v ∈ T)) := by
    intro f hf
    obtain ⟨i, hi⟩ := hT _ (hsq f hf)
    exact ⟨i, by simpa using hi⟩
  refine (tau4_le_card hS).trans (hcard ▸ ?_)
  exact Finset.card_le_card_of_injOn g (fun v hv => by simpa using hv) hg.injOn
end SizeRamsey.Plan
