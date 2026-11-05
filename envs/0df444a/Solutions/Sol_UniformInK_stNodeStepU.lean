-- Prove2me | solution 1 for UniformInK.stNodeStepU
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:15:10.963437+00:00
-- url     : https://prove2.me/submissions/51ed818f-478e-42e7-bfa6-f733253e04f4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs
import Definitions.Def_UniformInK_Spars_Step
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Sparsify_reduced_red
import Theorems.Thm_UniformInK_Step_sub_add
import Theorems.Thm_UniformInK_Step_card_over_le
import Theorems.Thm_UniformInK_Step_card_filter_subset_le_one
import Theorems.Thm_WidthK_Step_red_union
import Theorems.Thm_WidthK_Step_lay_nextN_self
import Theorems.Thm_WidthK_Step_lay_nextN_of_lt
import Theorems.Thm_WidthK_Step_lay_nextN_of_ne
import Theorems.Thm_WidthK_Step_notMem
import Theorems.Thm_WidthK_Step_nextA_zero
import Theorems.Thm_WidthK_Step_sum_nextA_of_lt
import Theorems.Thm_WidthK_Step_card_of_mem_petals
import Theorems.Thm_WidthK_card_petals
import Theorems.Thm_WidthK_Rule_add_light
import Theorems.Thm_WidthK_Rule_add_heavy
attribute [local fun_prop] Groundwork.PolyT.all

set_option autoImplicit false
section
section
open UniformInK
open Finset Groundwork Groundwork.Sparsify WidthK

namespace UniformInK
namespace Step

variable {α : Type*} [DecidableEq α]

section StepLemma

variable {θ : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}

private theorem toAddK (hA : AddU θ F A r) : AddK (fun i => 2 * θ (i - 1)) F A r where
  ssub := hA.ssub
  size := hA.size
  pos := hA.pos
  deg := by
    intro y
    have := hA.deg {y} (singleton_nonempty y) (by rw [card_singleton]; exact hA.pos)
    simpa only [singleton_subset_iff, card_singleton] using this

private theorem wsum_nextA_of_le (w a : ℕ → ℕ) (c : ℕ) {i r : ℕ} (hi : i ≤ r) :
    ∑ i' ∈ range i, w i' * nextA a r c i' = ∑ i' ∈ range i, w i' * a i' := by
  refine sum_congr rfl fun i' hi' => ?_
  have := mem_range.1 hi'
  simp only [nextA, if_neg (show i' ≠ r by omega), Nat.add_zero]

private theorem wsum_nextA_of_lt (w a : ℕ → ℕ) (c : ℕ) {i r : ℕ} (hi : r < i) :
    ∑ i' ∈ range i, w i' * nextA a r c i' = ∑ i' ∈ range i, w i' * a i' + w r * c := by
  simp only [nextA, Nat.mul_add, sum_add_distrib, mul_ite, Nat.mul_zero, sum_ite_eq', mem_range, if_pos hi]

private theorem card_lay_le (h : InvU θ F N a) (hA : AddU θ F A r) {i : ℕ} (hi : r ≤ i) :
    (lay N i).card ≤ ((lay N i).filter fun C => ∀ D ∈ A, ¬ D ⊆ C).card + A.card * (2 * θ (i - r)) := by
  have hsplit := card_filter_add_card_filter_not (s := lay N i) (fun C => ∀ D ∈ A, ¬ D ⊆ C)
  have hle : ((lay N i).filter fun C => ¬ ∀ D ∈ A, ¬ D ⊆ C).card ≤ A.card * (2 * θ (i - r)) := by
    refine le_trans (card_le_card ?_) (card_biUnion_le_card_mul A (fun D => (lay N i).filter fun C => D ⊆ C) (2 * θ (i - r)) ?_)
    · intro C hC
      obtain ⟨hCN, hex⟩ := mem_filter.1 hC
      simp only [not_forall, not_not] at hex
      obtain ⟨D, hD, hDC⟩ := hex
      exact mem_biUnion.2 ⟨D, hD, mem_filter.2 ⟨hCN, hDC⟩⟩
    · intro D hD
      have hne : D.Nonempty := by rw [← card_pos, hA.size D hD]; exact hA.pos
      have := h.deg i D hne (by rw [hA.size D hD]; exact hi)
      rwa [hA.size D hD] at this
  omega

private theorem inv_step (h : InvU θ F N a) (hA : AddU θ F A r) :
    InvU θ (Sparsify.red (F ∪ A)) (nextN N A) (nextA a r A.card) where
  red := reduced_red _
  sub := by
    rw [WidthK.Step.red_union h.red (toAddK hA)]
    exact union_subset_union_right (filter_subset_filter _ h.sub)
  deg := by
    intro i Y hY hYi
    by_cases hi : i = r
    · subst hi
      rw [WidthK.Step.lay_nextN_self h.red h.sub (toAddK hA), filter_union]
      have h1 : ((lay N i).filter fun C => Y ⊆ C).card ≤ (Sparsify.over F i Y).card := by
        apply card_le_card
        intro C hC
        obtain ⟨hCN, hYC⟩ := mem_filter.1 hC
        obtain ⟨hCN, hc⟩ := mem_filter.1 hCN
        exact mem_filter.2 ⟨h.sub hCN, hc, hYC⟩
      have := card_union_le (A.filter fun C => Y ⊆ C) ((lay N i).filter fun C => Y ⊆ C)
      have := hA.deg Y hY hYi
      omega
    · rw [WidthK.Step.lay_nextN_of_ne (toAddK hA) hi]
      exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (h.deg i Y hY hYi)
  acc := by
    intro i
    rcases lt_trichotomy i r with hi | hi | hi
    · rw [WidthK.Step.lay_nextN_of_lt (toAddK hA) hi, wsum_nextA_of_le _ a _ hi.le]
      simpa only [nextA, if_neg hi.ne, Nat.add_zero] using h.acc i
    · subst hi
      rw [WidthK.Step.lay_nextN_self h.red h.sub (toAddK hA), wsum_nextA_of_le _ a _ le_rfl, card_union_of_disjoint]
      · have := h.acc i
        simp only [nextA, if_true]
        omega
      · rw [disjoint_left]
        intro C hCA hCN
        exact WidthK.Step.notMem h.red (toAddK hA) hCA (h.sub (mem_filter.1 hCN).1)
    · rw [WidthK.Step.lay_nextN_of_ne (toAddK hA) hi.ne', wsum_nextA_of_lt _ a _ hi]
      have h1 := h.acc i
      have h2 := card_lay_le h hA hi.le
      simp only [nextA, if_neg hi.ne', Nat.add_zero]
      rw [Nat.mul_comm A.card] at h2
      omega

end StepLemma

variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}

private theorem add_light (hθ : ∀ i, 1 ≤ θ i) (hB : Rule θ k F j H) : AddU θ F {H} H.card where
  ssub := (hB.add_light hθ).ssub
  size := (hB.add_light hθ).size
  pos := (hB.add_light hθ).pos
  deg := by
    intro Y hY hYr
    have h1 := card_over_le hθ hB hB.heart.2.1 hY hYr
    have h2 : (({H} : Finset (Finset α)).filter fun D => Y ⊆ D).card ≤ 1 :=
      (card_le_card (filter_subset _ _)).trans (card_singleton H).le
    have h3 := hθ (H.card - Y.card)
    omega

private theorem add_heavy (hθ : ∀ i, 1 ≤ θ i) (hB : Rule θ k F j H) : AddU θ F (petals F j H) (j - H.card) where
  ssub := (hB.add_heavy hθ).ssub
  size := (hB.add_heavy hθ).size
  pos := (hB.add_heavy hθ).pos
  deg := by
    intro Y hY hYr
    have hH := card_pos.2 hB.heart.1
    have hlt := hB.heart.2.1
    have h1 := card_over_le hθ hB (r := j - H.card) (by omega) hY hYr
    have h2 : ((petals F j H).filter fun D => Y ⊆ D).card ≤ θ (j - H.card - Y.card) := by
      rcases hYr.eq_or_lt with he | hYlt
      · exact (card_filter_subset_le_one (fun Q hQ => WidthK.Step.card_of_mem_petals hQ) he).trans (hθ _)
      · by_cases hd : Disjoint H Y
        · have hc : (H ∪ Y).card = H.card + Y.card := card_union_of_disjoint hd
          have hYpos := card_pos.2 hY
          have hlt' : (Sparsify.over F j (H ∪ Y)).card < θ (j - H.card - Y.card) := by
            by_contra hcon
            refine hB.maxH (H ∪ Y) (by omega) ⟨hB.heart.1.mono subset_union_left, by omega, ?_⟩
            rw [hc, show j - (H.card + Y.card) = j - H.card - Y.card by omega]
            exact not_lt.1 hcon
          refine le_trans (le_trans (card_le_card ?_) (card_image_le (f := fun C => C \ H))) hlt'.le
          intro Q hQ
          obtain ⟨hQ, hYQ⟩ := mem_filter.1 hQ
          obtain ⟨C, hC, rfl⟩ := mem_image.1 hQ
          obtain ⟨hCF, hcC, hHC⟩ := mem_filter.1 hC
          exact mem_image.2 ⟨C, mem_filter.2 ⟨hCF, hcC, union_subset hHC (hYQ.trans sdiff_subset)⟩, rfl⟩
        · rw [filter_eq_empty_iff.2]
          · exact Nat.zero_le _
          · intro Q hQ hYQ
            obtain ⟨C, -, rfl⟩ := mem_image.1 hQ
            obtain ⟨x, hxH, hxY⟩ := not_disjoint_iff.1 hd
            exact (mem_sdiff.1 (hYQ hxY)).2 hxH
    omega

variable {τ p t : ℕ} {φ : Finset (Finset α)}

private theorem node_light (hθ : ∀ i, 1 ≤ θ i) (h : NodeU θ k τ φ F p t) (hB : Rule θ k F j H) :
    NodeU θ k τ φ (light F H) (p + 1) t := by
  have hA := add_light hθ hB
  refine ⟨sub_add h.1 hA, ?_⟩
  obtain ⟨-, N, a, hh, hI, ha0, hh1, hp, ht⟩ := h
  refine ⟨_, _, hh, inv_step hI hA, (WidthK.Step.nextA_zero a hA.pos _).trans ha0, fun r => ?_, ?_, ht⟩
  · exact (hh1 r).trans (Nat.le_add_right _ _)
  · rw [WidthK.Step.sum_nextA_of_lt a _ (lt_of_lt_of_le hB.heart.2.1 hB.le), card_singleton]
    omega

private theorem node_heavy (hθ : ∀ i, 1 ≤ θ i) (h : NodeU θ k τ φ F p t) (hB : Rule θ k F j H) :
    NodeU θ k τ φ (heavy F j H) (p + 1) (t + τ) := by
  have hA := add_heavy hθ hB
  have hH := card_pos.2 hB.heart.1
  have hlt := hB.heart.2.1
  have hj := hB.le
  have hr : j - H.card < k := by omega
  have hc : θ (j - H.card) ≤ (petals F j H).card := by rw [card_petals]; exact hB.heart.2.2
  refine ⟨sub_add h.1 hA, ?_⟩
  obtain ⟨-, N, a, hh, hI, ha0, hh1, hp, ht⟩ := h
  refine ⟨_, _, nextA hh (j - H.card) 1, inv_step hI hA, (WidthK.Step.nextA_zero a hA.pos _).trans ha0, fun r => ?_, ?_, ?_⟩
  · have := hh1 r
    simp only [nextA]
    split_ifs with hrr
    · subst hrr
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · simpa only [Nat.add_zero] using this
  · rw [WidthK.Step.sum_nextA_of_lt a _ hr]
    have := hθ (j - H.card)
    omega
  · rw [WidthK.Step.sum_nextA_of_lt hh _ hr, Nat.mul_add, Nat.mul_one]
    omega

end Step
end UniformInK

/-- Both children of a node are nodes: one more step, and τ more units at the heavy child. -/
theorem solution : StNodeStepU :=
  fun _ _ _ _ _ _ _ _ _ _ _ hθ h hB =>
    ⟨UniformInK.Step.node_light hθ h hB, UniformInK.Step.node_heavy hθ h hB⟩
