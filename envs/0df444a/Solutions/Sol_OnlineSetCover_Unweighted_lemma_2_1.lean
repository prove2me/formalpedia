-- Prove2me | solution 1 for OnlineSetCover.Unweighted.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T16:10:27.918786+00:00
-- url     : https://prove2.me/submissions/c0572f29-87c8-4516-aa95-0647240f683d

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlineSetCover_Unweighted_Algorithm
open OnlinePrimalDual.OnlineSetCover


namespace OnlineSetCover.Unweighted

lemma l21_aug_k_pos {x : ℝ} {k : ℕ} (hlt : x < 1) (hk : IsAugExponent x k) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; have := hk.1; simp at this; linarith
  · exact h

lemma l21_aug_bound {x : ℝ} {k : ℕ} (hlt : x < 1) (hk : IsAugExponent x k) :
    (2 : ℝ) ^ k * x ≤ 2 := by
  have hk1 := l21_aug_k_pos hlt hk
  have := hk.2 (k - 1) (by omega)
  have e : (2:ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [e]; nlinarith

lemma l21_step {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (OPT : Finset T) {s s' : State T} {j : E} {b : Bool}
    (hst : Step inst s j s' b) (hcov : coveredBy inst OPT j)
    (hpos : ∀ S, 0 < s.w S) (hle : ∀ S, s.w S ≤ 2) :
    (∀ S, 0 < s'.w S) ∧ (∀ S, s'.w S ≤ 2) ∧
      (if b then (1:ℝ) else 0) + ∑ S ∈ OPT, Real.logb 2 (s.w S) ≤
        ∑ S ∈ OPT, Real.logb 2 (s'.w S) := by
  cases hst with
  | noAug h => simp; exact ⟨hpos, hle⟩
  | aug k F hlt hk hF hcard hΦ =>
    have hk1 := l21_aug_k_pos hlt hk
    have hb := l21_aug_bound hlt hk
    have hSle : ∀ S ∈ inst.elemSets j, s.w S ≤ elementWeight inst s.w j := by
      intro S hS
      unfold elementWeight
      exact Finset.single_le_sum (f := s.w) (fun t _ => (hpos t).le) hS
    have h2k : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hge : ∀ S, s.w S ≤ augment inst s.w j k S := by
      intro S; unfold augment; split_ifs
      · nlinarith [hpos S]
      · exact le_rfl
    refine ⟨?_, ?_, ?_⟩
    · intro S; dsimp only; unfold augment; split_ifs
      · exact mul_pos (by positivity) (hpos S)
      · exact hpos S
    · intro S; dsimp only; unfold augment; split_ifs with hS
      · have := hSle S hS
        have : (2:ℝ) ^ k * s.w S ≤ 2 ^ k * elementWeight inst s.w j :=
          mul_le_mul_of_nonneg_left this (by positivity)
        linarith
      · exact hle S
    · obtain ⟨S0, hS0j, hS0O⟩ := hcov
      simp only [if_true]
      rw [← Finset.add_sum_erase _ _ hS0O, ← Finset.add_sum_erase _ _ hS0O]
      have h1 : 1 + Real.logb 2 (s.w S0) ≤ Real.logb 2 (augment inst s.w j k S0) := by
        unfold augment; rw [if_pos hS0j]
        rw [Real.logb_mul (by positivity) (hpos S0).ne', Real.logb_pow]
        simp
        have : (1:ℝ) ≤ k := by exact_mod_cast hk1
        linarith
      have h2 : ∑ S ∈ OPT.erase S0, Real.logb 2 (s.w S) ≤
          ∑ S ∈ OPT.erase S0, Real.logb 2 (augment inst s.w j k S) := by
        apply Finset.sum_le_sum; intro S _
        exact Real.logb_le_logb_of_le (by norm_num) (hpos S) (hge S)
      linarith

lemma l21_run {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (OPT : Finset T) {s s' : State T} {σ : List E} {a : ℕ}
    (hrun : RunFrom inst s σ s' a) (hcov : ∀ j ∈ σ, coveredBy inst OPT j)
    (hpos : ∀ S, 0 < s.w S) (hle : ∀ S, s.w S ≤ 2) :
    (∀ S, 0 < s'.w S) ∧ (∀ S, s'.w S ≤ 2) ∧
      (a : ℝ) + ∑ S ∈ OPT, Real.logb 2 (s.w S) ≤ ∑ S ∈ OPT, Real.logb 2 (s'.w S) := by
  induction hrun with
  | nil s => simp; exact ⟨hpos, hle⟩
  | @cons s s1 s2 j σ b a hst hr ih =>
    obtain ⟨p1, l1, i1⟩ := l21_step inst OPT hst (hcov j (by simp)) hpos hle
    obtain ⟨p2, l2, i2⟩ := ih (fun j hj => hcov j (by simp [hj])) p1 l1
    refine ⟨p2, l2, ?_⟩
    push_cast
    linarith

theorem l21_core {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (σ : List E) (OPT : Finset T)
    (hOPT : ∀ j ∈ σ, coveredBy inst OPT j)
    (s : State T) (a : ℕ) (hrun : Run inst σ s a) :
    (a : ℝ) ≤ (OPT.card : ℝ) * (Real.logb 2 (Fintype.card T) + 2) := by
  rcases Nat.eq_zero_or_pos (Fintype.card T) with hm | hm
  · -- no sets: σ must be empty
    have hOe : OPT = ∅ := by
      ext t; simp; have := Fintype.card_eq_zero_iff.mp hm; exact this.elim t
    cases σ with
    | nil =>
      unfold Run at hrun; cases hrun; simp [hOe]
    | cons j σ =>
      obtain ⟨t, _, ht⟩ := hOPT j (by simp)
      simp [hOe] at ht
  · have hmR : (0:ℝ) < Fintype.card T := by exact_mod_cast hm
    have hm1 : (1:ℝ) ≤ Fintype.card T := by exact_mod_cast hm
    have hpos : ∀ S, 0 < (initState T).w S := by
      intro S; simp [initState]; positivity
    have hle : ∀ S, (initState T).w S ≤ 2 := by
      intro S; simp only [initState]
      rw [div_le_iff₀ (by positivity)]; nlinarith
    obtain ⟨_, l2, i2⟩ := l21_run inst OPT hrun hOPT hpos hle
    have hfin : ∑ S ∈ OPT, Real.logb 2 (s.w S) ≤ OPT.card * 1 := by
      have : ∑ S ∈ OPT, Real.logb 2 (s.w S) ≤ ∑ S ∈ OPT, (1:ℝ) := by
        apply Finset.sum_le_sum; intro S _
        have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith [‹∀ S, 0 < s.w S› S]) (l2 S)
        simpa using this
      simpa using this
    have hinit : ∑ S ∈ OPT, Real.logb 2 ((initState T).w S) =
        OPT.card * (-(Real.logb 2 (Fintype.card T) + 1)) := by
      simp only [initState, Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [one_div, Real.logb_inv, Real.logb_mul (by norm_num) hmR.ne', Real.logb_self_eq_one (by norm_num)]
      ring
    rw [hinit] at i2
    nlinarith
end OnlineSetCover.Unweighted

open OnlineSetCover.Unweighted


theorem solution {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (σ : List E) (OPT : Finset T)
    (hOPT : ∀ j ∈ σ, coveredBy inst OPT j)
    (s : State T) (a : ℕ) (hrun : Run inst σ s a) :
    (a : ℝ) ≤ (OPT.card : ℝ) * (Real.logb 2 (Fintype.card T) + 2) := by
  exact l21_core inst σ OPT hOPT s a hrun
