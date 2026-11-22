-- Prove2me | solution 1 for VCDim_embed_ordinal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:43:54.393772+00:00
-- url     : https://prove2.me/submissions/fee6c8b6-46eb-414c-a308-75ed6d61e19e

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Littlestone
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Ordinal
public import Theorems.Thm_ordinalVCDim_inner_bddAbove
public import Theorems.Thm_ordinalVCDim_outer_bddAbove
section
@[expose] public section
universe u v
private theorem vcdim_card_le {X : Type u} {C : ConceptClass X Bool} {n : ℕ}
    (h : VCDim X C = n) {S : Finset X} (hS : Shatters X C S) : S.card ≤ n := by
  have : (S.card : WithTop ℕ) ≤ ↑n :=
    h ▸ le_iSup₂ (f := fun (S : Finset X) (_ : Shatters X C S) => (S.card : WithTop ℕ)) S hS
  exact WithTop.coe_le_coe.mp this
end
end

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution (X : Type u) (C : ConceptClass X Bool)
    (n : ℕ) (h : VCDim X C = n) : OrdinalVCDim X C = (n : Ordinal) := by
  unfold OrdinalVCDim
  apply le_antisymm
  · -- Upper bound: every shattered S has card ≤ n.
    refine ciSup_le' fun S => ciSup_le' fun hS => ?_
    exact Nat.cast_le.mpr (vcdim_card_le h hS)
  · -- Lower bound: VCDim = n ≥ 1 forces a shattered set with card = n.
    rcases Nat.eq_zero_or_pos n with rfl | _hn
    · exact bot_le
    · have hle : ∀ S, Shatters X C S → S.card ≤ n := fun S hS => vcdim_card_le h hS
      have ⟨S₀, hS₀_shat, hS₀_card⟩ : ∃ S₀, Shatters X C S₀ ∧ S₀.card = n := by
        by_contra h_none
        push Not at h_none
        have hcard : ∀ S, Shatters X C S → S.card ≤ n - 1 := by
          intro S hS
          have h1 : S.card ≤ n := hle S hS
          have h2 : S.card ≠ n := h_none S hS
          omega
        have hbound : VCDim X C ≤ ↑(n - 1) :=
          iSup₂_le fun S hS => WithTop.coe_le_coe.mpr (hcard S hS)
        rw [h] at hbound
        have : n ≤ n - 1 := WithTop.coe_le_coe.mp hbound
        omega
      calc (↑n : Ordinal) = ↑S₀.card := by exact_mod_cast hS₀_card.symm
        _ ≤ ⨆ (_ : Shatters X C S₀), ((S₀.card : ℕ) : Ordinal) :=
            le_ciSup (ordinalVCDim_inner_bddAbove X C S₀) hS₀_shat
        _ ≤ ⨆ S, ⨆ (_ : Shatters X C S), ((S.card : ℕ) : Ordinal) :=
            le_ciSup_of_le (ordinalVCDim_outer_bddAbove X C) S₀ le_rfl
