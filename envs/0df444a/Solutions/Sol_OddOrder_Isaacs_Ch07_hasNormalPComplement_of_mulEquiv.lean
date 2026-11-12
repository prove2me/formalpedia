-- Prove2me | solution 1 for OddOrder.Isaacs.Ch07.hasNormalPComplement_of_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:53:41.226531+00:00
-- url     : https://prove2.me/submissions/307ce765-8f8f-43d4-97a6-4baa0d57ef86

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJClose
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7B2_NormalJ_PComplement

-- ===== OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7B2_NormalJ_PComplement.lean =====
namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped commutatorElement

/-- Transport `OddOrder.Isaacs.Ch05.HasNormalPComplement` across a `MulEquiv`.

If `e : G ≃* H` and `G` has a normal `p`-complement, so does `H`. The complement is the
image of `G`'s complement under `e`. -/
theorem _root_.solution
    {G' H : Type*} [Group G'] [Group H]
    [Finite G'] [Finite H] {p : ℕ} [Fact p.Prime] (e : G' ≃* H)
    (hG : OddOrder.Isaacs.Ch05.HasNormalPComplement p G') :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p H := by
  classical
  obtain ⟨N, hN_normal, hN_compl⟩ := hG
  refine ⟨N.map e.toMonoidHom, ?_, ?_⟩
  · -- `N.map e` is normal in `H` because `e` is surjective.
    exact Subgroup.Normal.map hN_normal _ e.surjective
  · intro Q
    -- Pull `Q` back to a Sylow `p`-subgroup of `G'` via `e`.
    have h_range_top : (e.toMonoidHom).range = ⊤ :=
      MonoidHom.range_eq_top.mpr e.surjective
    have hQ_le_range : (Q : Subgroup H) ≤ (e.toMonoidHom).range := by
      rw [h_range_top]; exact le_top
    let Q' : Sylow p G' := Q.comapOfInjective e.toMonoidHom e.injective hQ_le_range
    have hQ'_compl : Subgroup.IsComplement' N (Q' : Subgroup G') := hN_compl Q'
    -- The image of Q' under e equals Q.
    have hQ'_eq : (Q' : Subgroup G') = (Q : Subgroup H).comap e.toMonoidHom := by
      simp [Q', Sylow.coe_comapOfInjective]
    have hQ_map : (Q' : Subgroup G').map e.toMonoidHom = (Q : Subgroup H) := by
      rw [hQ'_eq, Subgroup.map_comap_eq, h_range_top, top_inf_eq]
    -- |G'| = |H|, |N.map e| = |N|, |Q| = |Q'|.
    have hG_card : Nat.card G' = Nat.card H := Nat.card_congr e.toEquiv
    have hN_card : Nat.card (N.map e.toMonoidHom : Subgroup H) = Nat.card N := by
      exact
        (Nat.card_congr
          (Subgroup.equivMapOfInjective N e.toMonoidHom e.injective).toEquiv).symm
    have hQ_card : Nat.card (Q : Subgroup H) = Nat.card (Q' : Subgroup G') := by
      rw [← hQ_map]
      exact
        (Nat.card_congr
          (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv).symm
    -- Multiplicativity: |N.map e| * |Q| = |H|.
    have h_card_eq :
        Nat.card N * Nat.card (Q' : Subgroup G') = Nat.card G' :=
      hQ'_compl.card_mul_card
    have h_card_H :
        Nat.card (N.map e.toMonoidHom : Subgroup H) * Nat.card (Q : Subgroup H) =
          Nat.card H := by
      rw [hN_card, hQ_card, h_card_eq, hG_card]
    -- Coprimality: |N| coprime to p (from complement in G' with p-Sylow Q').
    have hp_ndvd_N : ¬ p ∣ Nat.card N := by
      rw [← hQ'_compl.index_eq_card]; exact Q'.not_dvd_index
    obtain ⟨k, hQ'_pow⟩ := IsPGroup.iff_card.mp Q'.isPGroup'
    have hp_prime : p.Prime := Fact.out
    have h_coprime' : Nat.Coprime (Nat.card N) (Nat.card (Q' : Subgroup G')) := by
      rw [hQ'_pow]
      exact ((hp_prime.coprime_iff_not_dvd.mpr hp_ndvd_N).symm).pow_right k
    have h_coprime :
        Nat.Coprime (Nat.card (N.map e.toMonoidHom : Subgroup H))
          (Nat.card (Q : Subgroup H)) := by
      rw [hN_card, hQ_card]; exact h_coprime'
    exact Subgroup.isComplement'_of_coprime h_card_H h_coprime

end OddOrder.Isaacs.Ch07
