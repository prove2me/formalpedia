-- Prove2me | solution 1 for SCCThm8.Rig.const_of_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:10.092179+00:00
-- url     : https://prove2.me/submissions/71c52575-d401-43d0-8bf2-3d59b5994dbf

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Theorems.Thm_SCCThm8_Rig_mem_sw
public import Theorems.Thm_SCCThm8_Rig_card_sw

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
namespace SCCThm8.Rig
theorem _root_.solution {X : Type*} {k : ℕ} (F : Finset (Fin n) → X)
    (h : ∀ A : Finset (Fin n), A.card = k → ∀ i j, i ∈ A → j ∉ A → F (sw A i j) = F A) :
    ∀ m, ∀ A A' : Finset (Fin n), A.card = k → A'.card = k → (A \ A').card = m → F A = F A' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro A A' hA hA' hm
  by_cases hsub : A ⊆ A'
  · rw [eq_of_subset_of_card_le hsub (by omega)]
  · obtain ⟨j, hjA, hjA'⟩ := not_subset.mp hsub
    have hsub' : ¬ A' ⊆ A := fun h' =>
      hjA' (by rw [eq_of_subset_of_card_le h' (by omega)]; exact hjA)
    obtain ⟨i, hiA', hiA⟩ := not_subset.mp hsub'
    rw [← h A hA j i hjA hiA]
    refine ih _ ?_ (sw A j i) A' (card_sw hA hjA hiA) hA' rfl
    rw [← hm]
    apply card_lt_card
    rw [ssubset_iff_of_subset]
    · refine ⟨j, mem_sdiff.mpr ⟨hjA, hjA'⟩, ?_⟩
      intro hx; rw [mem_sdiff, mem_sw] at hx
      rcases hx.1 with h' | ⟨h', _⟩
      · exact hiA (h' ▸ hjA)
      · exact h' rfl
    · intro x hx; rw [mem_sdiff, mem_sw] at hx; rw [mem_sdiff]
      rcases hx with ⟨rfl | ⟨_, h'⟩, h''⟩
      · exact absurd hiA' h''
      · exact ⟨h', h''⟩
end SCCThm8.Rig
