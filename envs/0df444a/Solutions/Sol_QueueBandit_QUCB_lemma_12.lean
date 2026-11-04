-- Prove2me | solution 1 for QueueBandit.QUCB.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T01:49:18.022181+00:00
-- url     : https://prove2.me/submissions/96bbcb57-a571-4901-8f0a-d18a8d100802

import Mathlib
import Definitions.Def_QueueBandit_QUCB_Model
import Definitions.Def_QueueBandit_QUCB_Algorithm1

namespace QueueBandit.QUCB.L12aux

open QueueBandit.QUCB

variable {U K : ℕ}

/-- One-slot increment of `Q_u − Q*_u` when `Q_u(j+1) > 0`. -/
theorem step_le (A : QUCBRule U K) (I : Instance U K) (u : Fin U) (j : ℕ) (ω : Ω U K)
    (hQ : A.Q I u (j + 1) ω ≠ 0) :
    (A.Q I u (j + 1) ω : ℤ) - (I.Qstar u (j + 1) ω : ℤ) ≤
      ((A.Q I u j ω : ℤ) - (I.Qstar u j ω : ℤ)) +
        ((explore (j + 1) ω : ℤ) +
          ∑ k ∈ Finset.univ.filter (fun k => k ≠ I.kstar u), (A.exploit I u k (j + 1) ω : ℤ)) := by
  classical
  have hQd : A.Q I u (j + 1) ω = A.Q I u j ω + I.A u (j + 1) ω - A.S I u (j + 1) ω := rfl
  have hQsd : I.Qstar u (j + 1) ω =
      I.Qstar u j ω + I.A u (j + 1) ω - I.R u (I.kstar u) (j + 1) ω := rfl
  set κ := (A.kappa I (j + 1) ω).1 u with hκ
  have hS : A.S I u (j + 1) ω = I.R u κ (j + 1) ω := rfl
  have hr1 : I.R u (I.kstar u) (j + 1) ω ≤ 1 := by unfold Instance.R; split_ifs <;> simp
  have hE1 : explore (U := U) (K := K) (j + 1) ω ≤ 1 := by unfold explore; split_ifs <;> simp
  have hsum_nn : (0 : ℤ) ≤ ∑ k ∈ Finset.univ.filter (fun k => k ≠ I.kstar u),
      (A.exploit I u k (j + 1) ω : ℤ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  -- increment bound `r - s`
  have hinc : (A.Q I u (j + 1) ω : ℤ) - (I.Qstar u (j + 1) ω : ℤ) ≤
      ((A.Q I u j ω : ℤ) - (I.Qstar u j ω : ℤ)) +
        ((I.R u (I.kstar u) (j + 1) ω : ℤ) - (A.S I u (j + 1) ω : ℤ)) := by
    rw [hQd] at hQ ⊢
    rw [hQsd]
    omega
  refine hinc.trans ?_
  by_cases hk : κ = I.kstar u
  · rw [hS, hk]
    have : (0 : ℤ) ≤ (explore (U := U) (K := K) (j + 1) ω : ℤ) := Nat.cast_nonneg _
    linarith
  · have hs0 : (0 : ℤ) ≤ (A.S I u (j + 1) ω : ℤ) := Nat.cast_nonneg _
    have hr1' : (I.R u (I.kstar u) (j + 1) ω : ℤ) ≤ 1 := by exact_mod_cast hr1
    by_cases he : explore (U := U) (K := K) (j + 1) ω = 0
    · have hex : A.exploit I u κ (j + 1) ω = 1 := by
        unfold QUCBRule.exploit
        rw [if_pos ⟨he, rfl⟩]
      have hmem : κ ∈ Finset.univ.filter (fun k => k ≠ I.kstar u) := by
        simp [hk]
      have hle : (A.exploit I u κ (j + 1) ω : ℤ) ≤ ∑ k ∈ Finset.univ.filter
          (fun k => k ≠ I.kstar u), (A.exploit I u k (j + 1) ω : ℤ) :=
        Finset.single_le_sum (f := fun k => (A.exploit I u k (j + 1) ω : ℤ))
          (fun _ _ => Nat.cast_nonneg _) hmem
      rw [hex] at hle
      have : (0 : ℤ) ≤ (explore (U := U) (K := K) (j + 1) ω : ℤ) := Nat.cast_nonneg _
      push_cast at hle
      linarith
    · have he1 : explore (U := U) (K := K) (j + 1) ω = 1 := by omega
      rw [he1]
      push_cast
      linarith

/-- The defining properties of `B_u(t)`. -/
theorem B_spec (A : QUCBRule U K) (I : Instance U K) (u : Fin U) (t : ℕ) (ω : Ω U K) :
    A.B I u t ω ≤ t ∧
      (A.Q I u (t - A.B I u t ω) ω : ℤ) - (I.Qstar u (t - A.B I u t ω) ω : ℤ) ≤ 0 ∧
      ∀ l, t - A.B I u t ω < l → l ≤ t → A.Q I u l ω ≠ 0 := by
  classical
  unfold QUCBRule.B
  split_ifs with h
  · have hs := Nat.find_spec h
    refine ⟨hs.1, ?_, ?_⟩
    · rw [hs.2]; simp
    · intro l hl hlt hQ
      have hlt' : t - l < Nat.find h := by omega
      have := Nat.find_min h hlt'
      apply this
      refine ⟨by omega, ?_⟩
      rw [show t - (t - l) = l by omega]
      exact hQ
  · refine ⟨le_rfl, ?_, ?_⟩
    · simp [QUCBRule.Q, Instance.Qstar]
    · intro l _ hlt hQ
      exact h ⟨t - l, by omega, by rw [show t - (t - l) = l by omega]; exact hQ⟩

end QueueBandit.QUCB.L12aux

open QueueBandit.QUCB QueueBandit.QUCB.L12aux in
theorem solution {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (I : Instance U K)
    (A : QUCBRule U K) (u : Fin U) (t : ℕ) (ht : 1 ≤ t) (ω : Ω U K) :
    (A.Q I u t ω : ℤ) - (I.Qstar u t ω : ℤ) ≤
      ∑ l ∈ Finset.Ioc (t - A.B I u t ω) t,
        ((explore l ω : ℤ) +
          ∑ k ∈ Finset.univ.filter (fun k => k ≠ I.kstar u), (A.exploit I u k l ω : ℤ)) := by
  obtain ⟨hBt, h0, hpos⟩ := B_spec A I u t ω
  set s0 := t - A.B I u t ω with hs0
  have key : ∀ k, s0 + k ≤ t →
      (A.Q I u (s0 + k) ω : ℤ) - (I.Qstar u (s0 + k) ω : ℤ) ≤
        ∑ l ∈ Finset.Ioc s0 (s0 + k),
          ((explore l ω : ℤ) +
            ∑ k ∈ Finset.univ.filter (fun k => k ≠ I.kstar u), (A.exploit I u k l ω : ℤ)) := by
    intro k
    induction k with
    | zero => intro _; simpa using h0
    | succ k ih =>
      intro hk
      rw [show s0 + (k + 1) = (s0 + k) + 1 by omega,
        Finset.sum_Ioc_succ_top (by omega : s0 ≤ s0 + k)]
      have hstep := step_le A I u (s0 + k) ω (hpos _ (by omega) (by omega))
      have := ih (by omega)
      linarith
  have := key (A.B I u t ω) (by omega)
  rwa [show s0 + A.B I u t ω = t by omega] at this
