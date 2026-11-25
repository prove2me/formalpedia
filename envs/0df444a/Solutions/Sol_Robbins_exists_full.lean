-- Prove2me | solution 1 for Robbins.exists_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:30:34.191605+00:00
-- url     : https://prove2.me/submissions/ed66bc98-6877-421e-8a29-e7b0825438fc

module
public import Mathlib
public import Definitions.Def_RobbinsLib_RobbinsAux
public import Theorems.Thm_Robbins_extend

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Robbins
variable {V : Type*} (G : SimpleGraph V)
variable {G}
open Classical
namespace Robbins
theorem _root_.solution [Finite V] (hb : ∀ e ∈ G.edgeSet, ¬ G.IsBridge e) :
    ∃ D : V → V → Prop, Inv G D ∧ ∀ a b, G.Adj a b → D a b ∨ D b a := by
  have := Fintype.ofFinite V
  let cnt : (V → V → Prop) → ℕ := fun D =>
    #{p : V × V | G.Adj p.1 p.2 ∧ ¬ D p.1 p.2 ∧ ¬ D p.2 p.1}
  suffices key : ∀ n, ∀ D : V → V → Prop, Inv G D → cnt D = n →
      ∃ D : V → V → Prop, Inv G D ∧ ∀ a b, G.Adj a b → D a b ∨ D b a by
    refine key _ (fun _ _ => False) ⟨fun _ _ h => h.elim, fun _ _ h => h.elim,
      fun _ _ h => h.elim⟩ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D hI hn
    by_cases hfull : ∀ a b, G.Adj a b → D a b ∨ D b a
    · exact ⟨D, hI, hfull⟩
    push Not at hfull
    obtain ⟨u, v, huv, hnu, hnv⟩ := hfull
    obtain ⟨D', hI', hmono, hD'⟩ := extend hI huv hnu hnv (hb _ huv)
    refine ih (cnt D') ?_ D' hI' rfl
    rw [← hn]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨(u, v), ?_, ?_⟩
      · simp [huv, hnu, hnv]
      · simp [hD']
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hp.1, fun h => hp.2.1 (hmono _ _ h), fun h => hp.2.2 (hmono _ _ h)⟩
end Robbins
