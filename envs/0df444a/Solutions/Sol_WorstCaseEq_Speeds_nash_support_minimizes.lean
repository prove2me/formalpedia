-- Prove2me | solution 1 for WorstCaseEq.Speeds.nash_support_minimizes
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:51:27.757994+00:00
-- url     : https://prove2.me/submissions/1192d76d-9cf7-42ab-b7df-1be6dd279e73

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WorstCaseEq_Speeds_Model



namespace WorstCaseEq.Speeds

open Finset

lemma wce_E_prod {n m : ℕ} (p : Fin n → Fin m → ℝ) (h : Fin n → Fin m → ℝ) :
    ∑ a : Fin n → Fin m, AGT.profileProb p a * ∏ k, h k (a k) = ∏ k, ∑ j, p k j * h k j := by
  rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [AGT.profileProb, ← Finset.prod_mul_distrib]

lemma wce_E_coord {n m : ℕ} (p : Fin n → Fin m → ℝ) (i : Fin n)
    (hp : ∀ k, k ≠ i → ∑ j, p k j = 1) (f : Fin m → ℝ) :
    ∑ a : Fin n → Fin m, AGT.profileProb p a * f (a i) = ∑ j, p i j * f j := by
  have h1 := wce_E_prod p (fun k j => if k = i then f j else 1)
  have h2 : ∀ a : Fin n → Fin m, (∏ k, (fun k j => if k = i then f j else 1) k (a k)) = f (a i) := by
    intro a; simp
  simp only [h2] at h1
  rw [h1, Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [hb, hp b hb]
  · simp

lemma wce_E_pair {n m : ℕ} (p : Fin n → Fin m → ℝ) (i k : Fin n) (hk : k ≠ i)
    (hp : ∀ k, k ≠ i → ∑ j, p k j = 1) (g : Fin m → ℝ) :
    ∑ a : Fin n → Fin m, AGT.profileProb p a * (if a k = a i then g (a i) else 0)
      = ∑ j, p i j * p k j * g j := by
  set H : Fin m → Fin n → Fin m → ℝ := fun j k' j' =>
    (if k' = i then (if j' = j then g j else 0) else 1) *
      (if k' = k then (if j' = j then 1 else 0) else 1) with hH
  have hprod : ∀ (j : Fin m) (a : Fin n → Fin m), (∏ k', H j k' (a k')) =
      (if a i = j then g j else 0) * (if a k = j then 1 else 0) := by
    intro j a
    rw [hH]; simp only
    rw [Finset.prod_mul_distrib]
    simp
  have hsum : ∀ a : Fin n → Fin m, (if a k = a i then g (a i) else 0) = ∑ j, ∏ k', H j k' (a k') := by
    intro a
    simp only [hprod]
    rw [Finset.sum_eq_single (a i)]
    · by_cases h : a k = a i <;> simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  simp only [hsum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wce_E_prod, Finset.prod_eq_mul i k (Ne.symm hk)]
  · rw [hH]; simp [Ne.symm hk, hk]; ring
  · intro c _ hc; rw [hH]; simp [hc.1, hc.2, hp c hc.1]
  · simp
  · simp


lemma wce_payoff_eq {n m : ℕ} (w : Fin n → ℝ) (s : Fin m → ℝ) (i : Fin n) (a : Fin n → Fin m) :
    payoff w s i a = -(w i / s (a i) +
      ∑ k ∈ Finset.univ.erase i, (if a k = a i then w k / s (a i) else 0)) := by
  unfold payoff WorstCaseEq.Identical.load
  rw [Finset.sum_filter, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [if_true, add_div, Finset.sum_div, ite_div, zero_div]

lemma wce_expPayoff {n m : ℕ} (w : Fin n → ℝ) (s : Fin m → ℝ) (q : Fin n → Fin m → ℝ) (i : Fin n)
    (hq : ∀ k, k ≠ i → ∑ j, q k j = 1) :
    AGT.expectedPayoff (payoff w s) q i = -∑ j, q i j * linkCost w s q i j := by
  unfold AGT.expectedPayoff
  simp only [wce_payoff_eq, mul_neg, mul_add, Finset.mul_sum, Finset.sum_neg_distrib,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm (t := Finset.univ.erase i)]
  have e1 := wce_E_coord q i hq (fun j => w i / s j)
  rw [e1]
  rw [Finset.sum_congr rfl (fun k hk => wce_E_pair q i k (Finset.ne_of_mem_erase hk) hq
    (fun j => w k / s j))]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold linkCost
  rw [add_div, Finset.sum_div, mul_add, Finset.mul_sum]
  refine congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun k _ => by ring)

lemma wce_linkCost_update {n m : ℕ} (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ)
    (i : Fin n) (τ : Fin m → ℝ) (j : Fin m) :
    linkCost w s (Function.update p i τ) i j = linkCost w s p i j := by
  unfold linkCost
  congr 2
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

/-- Nash characterization: for each agent `i`, the profile is Nash iff (with lotteries)
`∑ τ_j c_j ≥ ∑ p_j c_j` for all lotteries `τ`. -/
lemma wce_nash_iff {n m : ℕ} (w : Fin n → ℝ) (s : Fin m → ℝ) (p : Fin n → Fin m → ℝ)
    (hp : AGT.IsMixedProfile p) :
    IsNash w s p ↔ ∀ i (τ : Fin m → ℝ), AGT.IsLottery τ →
      ∑ j, p i j * linkCost w s p i j ≤ ∑ j, τ j * linkCost w s p i j := by
  unfold IsNash AGT.IsMixedNash
  have hq : ∀ i, ∀ k, k ≠ i → ∑ j, p k j = 1 := fun i k _ => (hp k).2
  constructor
  · rintro ⟨_, h⟩ i τ hτ
    have := h i τ hτ
    rw [wce_expPayoff w s _ i, wce_expPayoff w s _ i (hq i)] at this
    · simp only [Function.update_self, wce_linkCost_update] at this
      linarith
    · intro k hk; rw [Function.update_of_ne hk]; exact (hp k).2
  · intro h
    refine ⟨hp, fun i τ hτ => ?_⟩
    rw [wce_expPayoff w s _ i, wce_expPayoff w s _ i (hq i)]
    · simp only [Function.update_self, wce_linkCost_update]
      linarith [h i τ hτ]
    · intro k hk; rw [Function.update_of_ne hk]; exact (hp k).2


theorem nash_support_minimizes_core {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (s : Fin m → ℝ)
    (p : Fin n → Fin m → ℝ) (hp : IsNash w s p) :
    (∀ i j, 0 < p i j → ∀ j', linkCost w s p i j ≤ linkCost w s p i j') ∧
      ∀ i, expCost w s p i = Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i) := by
  have hprof : AGT.IsMixedProfile p := hp.1
  have hN := (wce_nash_iff w s p hprof).1 hp
  have hexp : ∀ i, expCost w s p i = ∑ j, p i j * linkCost w s p i j := by
    intro i
    unfold expCost
    rw [wce_expPayoff w s p i (fun k _ => (hprof k).2), neg_neg]
  -- the expected cost is at most every link cost
  have hle : ∀ i j', ∑ j, p i j * linkCost w s p i j ≤ linkCost w s p i j' := by
    intro i j'
    have := hN i (fun j => if j = j' then 1 else 0) ⟨fun a => by dsimp only; split_ifs <;> norm_num, by simp⟩
    simpa using this
  -- and at least the minimum
  have hge : ∀ i, Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i) ≤
      ∑ j, p i j * linkCost w s p i j := by
    intro i
    set μ := Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i)
    calc μ = ∑ j, p i j * μ := by rw [← Finset.sum_mul, (hprof i).2, one_mul]
      _ ≤ ∑ j, p i j * linkCost w s p i j := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ (Finset.mem_univ j)) ((hprof i).1 j)
  have heq : ∀ i, ∑ j, p i j * linkCost w s p i j =
      Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i) := by
    intro i
    refine le_antisymm ?_ (hge i)
    obtain ⟨j0, _, hj0⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin m))
      (linkCost w s p i)
    rw [hj0]; exact hle i j0
  refine ⟨fun i j hj j' => ?_, fun i => by rw [hexp, heq]⟩
  set μ := Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i) with hμ
  have hsum : ∑ k, p i k * (linkCost w s p i k - μ) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (hprof i).2, one_mul]
    rw [heq i]; ring
  have hterm : p i j * (linkCost w s p i j - μ) ≤ ∑ k, p i k * (linkCost w s p i k - μ) := by
    refine Finset.single_le_sum (f := fun k => p i k * (linkCost w s p i k - μ))
      (fun k _ => mul_nonneg ((hprof i).1 k) (sub_nonneg.2 (Finset.inf'_le _ (Finset.mem_univ k))))
      (Finset.mem_univ j)
  rw [hsum] at hterm
  have h1 : linkCost w s p i j - μ ≤ 0 := by
    by_contra hc; rw [not_le] at hc; linarith [mul_pos hj hc]
  have h2 : μ ≤ linkCost w s p i j' := Finset.inf'_le _ (Finset.mem_univ j')
  linarith

end WorstCaseEq.Speeds

open WorstCaseEq.Speeds


theorem solution {n m : ℕ} [NeZero m] (w : Fin n → ℝ) (s : Fin m → ℝ)
    (p : Fin n → Fin m → ℝ) (hp : IsNash w s p) :
    (∀ i j, 0 < p i j → ∀ j', linkCost w s p i j ≤ linkCost w s p i j') ∧
      ∀ i, expCost w s p i = Finset.univ.inf' Finset.univ_nonempty (linkCost w s p i) := by
  exact nash_support_minimizes_core w s p hp
