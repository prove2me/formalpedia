-- Prove2me | solution 1 for Subgroup.thompsonJ_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T04:48:30.309164+00:00
-- url     : https://prove2.me/submissions/76547642-2c6d-4dbc-b448-c75e3f834002

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/ThompsonSubgroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas

-- ===== OddOrder/GroupTheory/ThompsonSubgroup.lean =====
namespace Subgroup

variable {G : Type*} [Group G]

/-- The trivial subgroup `⊥` is `p`-elementary abelian for any `p`. -/
theorem bot_isElementaryAbelian (p : ℕ) :
    (⊥ : Subgroup G).IsElementaryAbelian p := by
  refine ⟨?_, ?_⟩
  · intro x y
    exact Subsingleton.elim _ _
  · intro x
    have hx : x = 1 := Subsingleton.elim x 1
    rw [hx, one_pow]

/-- `[Finite G]` のもとで `maxElemAbelianIn P p` は非空 (`⊥` が常に元). -/
theorem maxElemAbelianIn_nonempty [Finite G] (P : Subgroup G) (p : ℕ) :
    (maxElemAbelianIn P p).Nonempty := by
  -- S = {F ≤ P | F elem ab} は有限・非空 (⊥ ∈ S).
  have hUniv : (Set.univ : Set (Subgroup G)).Finite := Set.finite_univ
  have hS_fin : {F : Subgroup G | F ≤ P ∧ F.IsElementaryAbelian p}.Finite :=
    hUniv.subset (fun _ _ => Set.mem_univ _)
  have hS_ne : {F : Subgroup G | F ≤ P ∧ F.IsElementaryAbelian p}.Nonempty :=
    ⟨⊥, bot_le, bot_isElementaryAbelian p⟩
  -- 最大位数の元 E を取得.
  obtain ⟨E, hE_S, hE_max⟩ :=
    Set.exists_max_image
      {F : Subgroup G | F ≤ P ∧ F.IsElementaryAbelian p}
      (fun F => Nat.card F) hS_fin hS_ne
  refine ⟨E, hE_S.1, hE_S.2, ?_⟩
  intro F hF_P hF_el
  exact hE_max F ⟨hF_P, hF_el⟩

/-- **`J(P) ≠ ⊥` for a nontrivial finite `p`-group `P`**.

A nontrivial `p`-group contains an element of order `p` (Cauchy), generating a
cyclic — hence `p`-elementary abelian — subgroup of order `p`.  Thus the
maximum-order elementary abelian subgroup of `P` has order `≥ p > 1`, so
`J(P) ≠ ⊥`. -/
theorem _root_.solution [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP_pgroup : IsPGroup p ↥P) (hP_ne_bot : P ≠ ⊥) :
    thompsonJ P p ≠ ⊥ := by
  classical
  -- A maximum-order elementary abelian subgroup `E` of `P` exists.
  obtain ⟨E, hE_le, hE_el, hE_max⟩ := maxElemAbelianIn_nonempty P p
  -- `p ∣ |P|` (nontrivial `p`-group), so there is an order-`p` element `x ∈ P`.
  have hp_dvd : p ∣ Nat.card ↥P := by
    obtain ⟨n, hn⟩ := hP_pgroup.exists_card_eq
    have hn_pos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | h
      · exfalso
        rw [h0, pow_zero] at hn
        exact hP_ne_bot (Subgroup.card_eq_one.mp hn)
      · exact h
    rw [hn]; exact dvd_pow_self p hn_pos.ne'
  obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  -- `C := zpowers x.val ≤ P` is `p`-elementary abelian of order `p`.
  set C : Subgroup G := Subgroup.zpowers (x : G) with hC_def
  have hxG_ord : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe, hx_ord]
  have hC_le_P : C ≤ P := by
    rw [hC_def]
    exact (Subgroup.zpowers_le).mpr x.2
  have hC_card : Nat.card ↥C = p := by rw [hC_def, Nat.card_zpowers, hxG_ord]
  have hC_el : C.IsElementaryAbelian p := by
    refine ⟨fun a b => ?_, fun a => ?_⟩
    · -- `C = zpowers x` is commutative: `↑a, ↑b` are powers of `x`, which commute.
      apply Subtype.ext
      have ha : (a : G) ∈ Subgroup.zpowers (x : G) := a.2
      have hb : (b : G) ∈ Subgroup.zpowers (x : G) := b.2
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
      simp only [Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, add_comm]
    · -- every element of `C` has order dividing `p`, so `a ^ p = 1`.
      have hdvd : orderOf a ∣ p := by
        rw [← hC_card]; exact _root_.orderOf_dvd_natCard a
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
  -- `|C| = p ≤ |E|`, so `E ≠ ⊥`, and `E ≤ J(P)`.
  have hp_le_E : p ≤ Nat.card ↥E := hC_card ▸ hE_max C hC_le_P hC_el
  have hE_ne_bot : E ≠ ⊥ := by
    intro hbot
    rw [hbot] at hp_le_E
    simp only [Subgroup.card_bot] at hp_le_E
    exact (Fact.out (p := p.Prime)).one_lt.not_ge hp_le_E
  have hE_le_J : E ≤ thompsonJ P p :=
    le_thompsonJ_of_mem_maxElemAbelianIn ⟨hE_le, hE_el, hE_max⟩
  intro hJ_bot
  rw [hJ_bot, le_bot_iff] at hE_le_J
  exact hE_ne_bot hE_le_J

end Subgroup
