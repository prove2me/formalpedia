-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.coprime_card_Q_card_VW2
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:11:33.390433+00:00
-- url     : https://prove2.me/submissions/f9f5c34b-1fec-4eb7-8a59-da06d1ded255

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndTBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

-- ===== OddOrder/Peterfalvi/S15_SAndTBasic.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (13.16), the `W₁`-side coprime-action datum**: `Coprime |Q| |V ⋊ W₂|` — the
complement `V ⋊ W₂` acts coprimely on the Fitting kernel `Q = T_F`.  The `T`-side dual of
`coprime_card_P_card_UW1`.

`Q = T_F` is the normal nilpotent Hall subgroup of `T` (`maxNilpotentNormalHall`, so
`Coprime |Q| [T:Q]`), and `V ⋊ W₂` complements `Q` in `T`: from the honest `Hypothesis` fields
`W2_isComplement_T_deriv` (`M' ⋊ W₂ = T`) and `Q_inf_V_eq_bot`/`T_deriv_eq_QV` (`Q ⋊ V = M'`) one
reads off `Q ⊓ (V ⊔ W₂) = ⊥` and `Q ⊔ (V ⊔ W₂) = T`, so `[T:Q] = |V ⊔ W₂|`.  **Fully honest /
ungated** — both complements come from the §16 constructor
(`typeP_derivedInG_isComplement_kappaHall`
/ `exists_kappaHall_invariant_complement_to_MF`, via `T_nonI`, not (14.9)); no dependence on the
then-sorried `reconciled_typePData_T`. -/
theorem _root_.solution [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.Coprime (Nat.card ↥hyp.Q) (Nat.card ↥(hyp.V ⊔ hyp.W2)) := by
  -- Fully honest (ungated): built from the `Hypothesis` fields `Q_inf_V_eq_bot` (`Q ⊓ V = ⊥`) and
  -- `W2_isComplement_T_deriv` (`T = T' ⋊ W₂`), both threaded from the §16 constructor's
  -- `exists_kappaHall_invariant_complement_to_MF` / `typeP_derivedInG_isComplement_kappaHall`
  -- (ungated by (14.9)).  No longer routed through the then-sorried `reconciled_typePData_T`.
  have hM'_le_T : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have hQ_le_M' : hyp.Q ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_left
  have hV_le_M' : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
  have hQ_le_T : hyp.Q ≤ hyp.T := hQ_le_M'.trans hM'_le_T
  have hW2_le_T : hyp.W2 ≤ hyp.T := by
    have h1 : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
    have h2 : hyp.W ≤ hyp.T := by rw [hyp.W_eq_inter]; exact inf_le_right
    exact h1.trans h2
  have hVW2_le_T : hyp.V ⊔ hyp.W2 ≤ hyp.T := sup_le (hV_le_M'.trans hM'_le_T) hW2_le_T
  -- `Q ⊓ V = ⊥` (`Q_inf_V_eq_bot`).
  have hdisj : hyp.Q ⊓ hyp.V = ⊥ := hyp.Q_inf_V_eq_bot
  -- `M' ⊓ W₂ = ⊥` from the complement `T = T' ⋊ W₂` (`W2_isComplement_T_deriv`).
  have hM'W2 : derivedInG hyp.T ⊓ hyp.W2 = ⊥ := by
    have hd := disjoint_iff.mp hyp.W2_isComplement_T_deriv.disjoint
    rw [eq_bot_iff]; rintro x ⟨hxM', hxW2⟩
    have hxT : x ∈ hyp.T := hM'_le_T hxM'
    have hmem : (⟨x, hxT⟩ : ↥hyp.T) ∈
        ((derivedInG hyp.T).subgroupOf hyp.T) ⊓ (hyp.W2.subgroupOf hyp.T) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxM', Subgroup.mem_subgroupOf.mpr hxW2⟩
    rw [hd, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; simpa using Subtype.ext_iff.mp hmem
  -- `Q ⊔ (V ⊔ W₂) = T` from `T = T' ⋊ W₂` and `T' = Q ⊔ V`.
  have hTsup : hyp.Q ⊔ (hyp.V ⊔ hyp.W2) = hyp.T := by
    have htop := hyp.W2_isComplement_T_deriv.sup_eq_top
    have hmap := congrArg (Subgroup.map hyp.T.subtype) htop
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hM'_le_T,
      Subgroup.map_subgroupOf_eq_of_le hW2_le_T, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
    rw [hyp.T_deriv_eq_QV] at hmap
    rw [← sup_assoc]; exact hmap
  -- `Q ⊓ (V ⊔ W₂) = ⊥`.
  have hQVW2_disj : hyp.Q ⊓ (hyp.V ⊔ hyp.W2) = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxQ, hxVW2⟩ := Subgroup.mem_inf.mp hx
    have hxVW2' : (x : G) ∈ (↑(hyp.V ⊔ hyp.W2) : Set G) := hxVW2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left hyp.V hyp.W2 hyp.W2_normalizes_V] at hxVW2'
    obtain ⟨v, hv, w, hw, hvw⟩ := Set.mem_mul.mp hxVW2'
    have hwM' : w ∈ derivedInG hyp.T := by
      have : w = v⁻¹ * x := by rw [← hvw]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hV_le_M' (SetLike.mem_coe.mp hv)))
        (hQ_le_M' hxQ)
    have hw1 : w = 1 := by
      have : w ∈ derivedInG hyp.T ⊓ hyp.W2 := Subgroup.mem_inf.mpr ⟨hwM', SetLike.mem_coe.mp hw⟩
      rwa [hM'W2, Subgroup.mem_bot] at this
    have hxv : x = v := by rw [← hvw, hw1, mul_one]
    have hxQV : x ∈ hyp.Q ⊓ hyp.V := Subgroup.mem_inf.mpr ⟨hxQ, hxv ▸ SetLike.mem_coe.mp hv⟩
    rwa [hdisj, Subgroup.mem_bot] at hxQV
  -- `V ⋊ W₂` complements `Q` in `↥T`; hence `[T:Q] = |V ⋊ W₂|`.
  have hT_norm_Q : hyp.T ≤ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  have hQnorm : (hyp.Q.subgroupOf hyp.T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le_T).mpr hT_norm_Q
  have hcompl : Subgroup.IsComplement' ((hyp.V ⊔ hyp.W2).subgroupOf hyp.T)
      (hyp.Q.subgroupOf hyp.T) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [disjoint_iff, eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hy
      have hyQV : (y : G) ∈ hyp.Q ⊓ (hyp.V ⊔ hyp.W2) := ⟨hy.2, hy.1⟩
      rw [hQVW2_disj, Subgroup.mem_bot] at hyQV
      rw [Subgroup.mem_bot]; exact Subtype.ext hyQV
    · have hsup : ((hyp.V ⊔ hyp.W2).subgroupOf hyp.T) ⊔ (hyp.Q.subgroupOf hyp.T) = ⊤ := by
        rw [sup_comm, ← Subgroup.subgroupOf_sup hQ_le_T hVW2_le_T, hTsup, Subgroup.subgroupOf_self]
      rw [← Subgroup.mul_normal, hsup, Subgroup.coe_top]
  have hindex : (hyp.Q.subgroupOf hyp.T).index = Nat.card ↥(hyp.V ⊔ hyp.W2) := by
    rw [hcompl.index_eq_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW2_le_T).toEquiv
  -- `Q` is Hall in `T`: `Coprime |Q| [T:Q]`.
  have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.T
  rw [← hyp.Q_eq_TF] at hHall
  have hcopIdx : Nat.Coprime (Nat.card ↥hyp.Q) (hyp.Q.subgroupOf hyp.T).index := by
    have hcard_eq : Nat.card ↥(hyp.Q.subgroupOf hyp.T) = Nat.card ↥hyp.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv
    exact hcard_eq ▸ OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
  rw [hindex] at hcopIdx
  exact hcopIdx

end OddOrder.Peterfalvi.S15
