-- Prove2me | solution 1 for OrderSelector.wellOrdered_of_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:47:09.889356+00:00
-- url     : https://prove2.me/submissions/7e584cbb-2884-4845-9fae-dfdbfa880e8f

import Mathlib.Order.Preorder.Chain
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.WellFoundedSet
import Definitions.Def_ChainBounding_Solution
import Theorems.Thm_OrderSelector_good_of_isSegment

set_option autoImplicit true
variable {α : Type*}
open Set IsChain
variable [PartialOrder α] [OrderSelector α]
open OrderExpander
open OrderSelector
namespace OrderSelector
theorem _root_.solution {C : Set α} (hC : Good C) (X : Set α) (hXC : X ⊆ C)
    (hne : X.Nonempty) : ∃ m ∈ X, ∀ y ∈ X, m ≤ y := by
  -- `S` is the set of strict lower bounds of `X` in `C`.
  let S := {c : α | c ∈ C ∧ ∀ y ∈ X, c < y}
  have Sseg : S ⊏ C := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact fun c hc => hc.1
    · exact fun c hc s hs cle => ⟨hc, fun z hz => lt_of_le_of_lt cle (hs.2 z hz)⟩
    · intro hEq
      obtain ⟨x₀, hx₀⟩ := hne
      have hx₀S : x₀ ∈ S := by rw [hEq]; exact hXC hx₀
      exact lt_irrefl x₀ (hx₀S.2 x₀ hx₀)
  have goodS := hC.2 Sseg
  -- `f S` lies in `g S` and in `C`, but not in `S`.
  have hfSg : f S ∈ g S := by
    rw [g_def]
    exact mem_union_right S rfl
  have hfC : f S ∈ C := goodS.2.1 hfSg
  have hfS_not : f S ∉ S := by
    intro h
    refine goodS.1.2 ?_
    rw [g_def, union_eq_self_of_subset_right (show {f S} ⊆ S from fun c hc => by
      rw [mem_singleton_iff] at hc
      rw [hc]
      exact h)]
  -- `f S` is a lower bound of `X`.
  have lower : ∀ y ∈ X, f S ≤ y := by
    intro y hy
    have hyC : y ∈ C := hXC hy
    have Dseg : {c : α | c ∈ C ∧ c ≤ y} ⊑ C :=
      ⟨fun c hc => hc.1, fun c hc s hs cle => ⟨hc, le_trans cle hs.2⟩⟩
    have hDgood : Good {c : α | c ∈ C ∧ c ≤ y} := good_of_isSegment hC Dseg
    have SsegD : S ⊏ {c : α | c ∈ C ∧ c ≤ y} := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact fun s hs => ⟨hs.1, le_of_lt (hs.2 y hy)⟩
      · exact fun c hc s hs cle => ⟨hc.1, fun z hz => lt_of_le_of_lt cle (hs.2 z hz)⟩
      · intro hEq
        have hyD : y ∈ {c : α | c ∈ C ∧ c ≤ y} := ⟨hyC, le_refl y⟩
        have hyS : y ∈ S := by rw [hEq]; exact hyD
        exact lt_irrefl y (hyS.2 y hy)
    have hfD : f S ∈ {c : α | c ∈ C ∧ c ≤ y} := (hDgood.2 SsegD).2.1 hfSg
    exact hfD.2
  -- Some element of `X` lies above `f S`.
  have step3 : ∃ x ∈ X, x ≤ f S := by
    by_contra h
    push Not at h
    have hfS : f S ∈ S := by
      refine ⟨hfC, fun z hz => ?_⟩
      have hcomp : f S ≤ z ∨ z ≤ f S :=
        hC.1 hfC (hXC hz) fun hh => h z hz (by rw [hh])
      rcases hcomp with hle | hge
      · exact lt_of_le_of_ne hle fun hh => h z hz (by rw [← hh])
      · exact absurd hge (h z hz)
    exact hfS_not hfS
  obtain ⟨x₀, hx₀X, hx₀f⟩ := step3
  have hfx : f S = x₀ := le_antisymm (lower x₀ hx₀X) hx₀f
  refine ⟨f S, ?_, lower⟩
  rw [hfx]
  exact hx₀X
end OrderSelector
