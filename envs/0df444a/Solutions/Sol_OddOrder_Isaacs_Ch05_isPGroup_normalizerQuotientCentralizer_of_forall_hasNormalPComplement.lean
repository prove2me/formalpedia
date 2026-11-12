-- Prove2me | solution 1 for OddOrder.Isaacs.Ch05.isPGroup_normalizerQuotientCentralizer_of_forall_hasNormalPComplement
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T05:31:53.177089+00:00
-- url     : https://prove2.me/submissions/18545a2a-2da7-44e9-9041-da71fa40b683

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch05_Transfer/Main.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Nilpotent

-- ===== OddOrder/Isaacs/Ch05_Transfer/Main.lean =====
open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

open Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

section

/-- **Isaacs Lem 5.27 part 2 (2 ⇒ 3)**: 仮定「∀ 非自明 p-subgroup `X` ⊆ `G`,
`N_G(X)` が normal p-complement を持つ」 ⇒ 任意 p-subgroup `X` で
`↥N_G(X) / (C_G(X)).subgroupOf N_G(X)` は p-group.

**証明** (Isaacs p.174):
* `X = ⊥` の場合: `centralizer (⊥ : Set G) = ⊤` (1 と全 g が可換) ⇒
  `subgroupOf normalizer = ⊤` ⇒ 商 ↥(normalizer ⊥) ⧸ ⊤ は Subsingleton ⇒ p-group.
* `X ≠ ⊥` の場合: 仮定で `normalizer X` の normal p-complement `K'` を得る.
  `X.subgroupOf (normalizer X)` (`X_n`) は normal (`normal_in_normalizer`),
  `K'` も normal. `K' ⊓ X_n = ⊥` (|K'| coprime to p, |X_n| = |X| p-power,
  `inf_eq_bot_of_coprime`).
  `[K', X_n] ≤ K' ⊓ X_n = ⊥` (`commutator_le_inf` with両 normal) ⇒
  `K' ≤ centralizer X_n` (`commutator_eq_bot_iff_le_centralizer`).
  座標 ↥(normalizer X) → G で `K' ≤ (centralizer X).subgroupOf (normalizer X)` (`C_n`).
  `↥(normalizer X) ⧸ K'` は p-group (Sylow Q complement), `↥(normalizer X) ⧸ C_n` は
  その quotient (`QuotientGroup.map (id) ... K'≤C_n`) ⇒ `IsPGroup.of_surjective` で p-group. -/
theorem _root_.solution
    [Finite G] {p : ℕ} [Fact p.Prime]
    (h : ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup p X →
        HasNormalPComplement p ↥(Subgroup.normalizer (X : Set G)))
    (X : Subgroup G) (hXp : IsPGroup p X) :
    IsPGroup p (↥(Subgroup.normalizer (X : Set G)) ⧸
      (Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  -- 統一戦略: `C_n := (centralizer X).subgroupOf (normalizer X)` の `index` が `p` 乗
  -- であることを示し, `IsPGroup.of_card` を介して `↥N ⧸ C_n` が p-group であることを導く.
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hN_def
  -- ∃ b, C_n.index = p^b を示せばよい
  suffices h_idx_pow : ∃ b, ((Subgroup.centralizer (X : Set G)).subgroupOf N).index = p ^ b by
    obtain ⟨b, hb⟩ := h_idx_pow
    refine IsPGroup.of_card (n := b) ?_
    rw [← Subgroup.index_eq_card]; exact hb
  -- 場合分け
  by_cases hX_bot : X = ⊥
  · -- X = ⊥: centralizer = ⊤ ⇒ subgroupOf = ⊤ ⇒ index = 1 = p^0
    refine ⟨0, ?_⟩
    rw [pow_zero]
    have hSubgroup_top : (Subgroup.centralizer (X : Set G)).subgroupOf N = ⊤ := by
      ext ⟨g, hg⟩
      refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro b hb
      subst hX_bot
      rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hb
      rw [hb, one_mul, mul_one]
    rw [hSubgroup_top, Subgroup.index_top]
  · -- X ≠ ⊥: hypothesis gives K' normal p-complement, K' ≤ C_n, C_n.index ∣ K'.index = p^a
    obtain ⟨K', hK'_normal, hK'_compl⟩ := h X hX_bot hXp
    have : K'.Normal := hK'_normal
    let X_n : Subgroup ↥N := X.subgroupOf N
    have hX_n_normal : X_n.Normal := by
      change (X.subgroupOf (Subgroup.normalizer (X : Set G))).Normal
      exact Subgroup.normal_in_normalizer
    -- Sylow Q in ↥N
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p ↥N))
    have hQ_compl : Subgroup.IsComplement' K' (Q : Subgroup ↥N) := hK'_compl Q
    -- ¬ p ∣ |K'| (Sylow not_dvd_index + IsComplement'.index_eq_card)
    have h_p_ndvd_K' : ¬ p ∣ Nat.card ↥K' := by
      rw [← hQ_compl.index_eq_card]; exact Q.not_dvd_index
    -- X_n p-group (|X_n| = |X|)
    have h_X_n_pg : IsPGroup p X_n := by
      have hX_le_N : X ≤ N := Subgroup.le_normalizer
      have h_card_eq : Nat.card ↥X_n = Nat.card ↥X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_le_N).toEquiv
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hXp
      exact IsPGroup.of_card (h_card_eq.trans hk)
    -- K' ⊓ X_n = ⊥ (coprime cards)
    have h_inf_bot : K' ⊓ X_n = ⊥ := by
      refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
      obtain ⟨k, hX_n_card⟩ := IsPGroup.iff_card.mp h_X_n_pg
      rw [hX_n_card]
      exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h_p_ndvd_K').symm).pow_right k
    -- [K', X_n] = ⊥ (commutator_le_inf with K', X_n both normal)
    have h_comm_bot : ⁅K', X_n⁆ = ⊥ :=
      le_bot_iff.mp (h_inf_bot ▸ Subgroup.commutator_le_inf K' X_n)
    -- K' ≤ centralizer (X_n : Set ↥N)
    have h_K'_cent : K' ≤ Subgroup.centralizer (X_n : Set ↥N) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h_comm_bot
    -- K' ≤ (centralizer X).subgroupOf N
    have h_K'_le_C_n : K' ≤ (Subgroup.centralizer (X : Set G)).subgroupOf N := by
      intro k hk
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro x hxX
      have hxN : x ∈ N := Subgroup.le_normalizer hxX
      have hx_in_Xn : (⟨x, hxN⟩ : ↥N) ∈ X_n := by
        change (⟨x, hxN⟩ : ↥N) ∈ X.subgroupOf N
        rw [Subgroup.mem_subgroupOf]; exact hxX
      have hkx_eq : (⟨x, hxN⟩ : ↥N) * k = k * (⟨x, hxN⟩ : ↥N) :=
        Subgroup.mem_centralizer_iff.mp (h_K'_cent hk) ⟨x, hxN⟩ hx_in_Xn
      exact congrArg Subtype.val hkx_eq
    -- K'.index = |Q| (IsComplement'.symm.index_eq_card)
    have hK'_idx : K'.index = Nat.card ↥(Q : Subgroup ↥N) := hQ_compl.symm.index_eq_card
    -- K'.index = p^a (Q is p-group)
    obtain ⟨a, hKa⟩ : ∃ a, K'.index = p ^ a := by
      rw [hK'_idx]; exact IsPGroup.iff_card.mp Q.isPGroup'
    -- C_n.index ∣ K'.index (K' ≤ C_n)
    have hC_n_idx_dvd : ((Subgroup.centralizer (X : Set G)).subgroupOf N).index ∣ K'.index :=
      Subgroup.index_dvd_of_le h_K'_le_C_n
    -- C_n.index = p^b for some b ≤ a
    rcases (Nat.dvd_prime_pow Fact.out).mp (hKa ▸ hC_n_idx_dvd) with ⟨b, _, hb⟩
    exact ⟨b, hb⟩

end

end OddOrder.Isaacs.Ch05
