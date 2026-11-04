-- Prove2me | solution 1 for PerishBaseStock.Lifo.ec_18
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T22:14:59.657344+00:00
-- url     : https://prove2.me/submissions/c5fb6364-a746-458d-9b3d-322efa764681

import Definitions.Def_PerishBaseStock_Lifo_Heuristic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic

namespace L5D
set_option linter.unusedSectionVars false
open PerishBaseStock.Lifo

variable {m : ℕ}

lemma cum_zero (x : PerishBaseStock.Lifetime.State m) : cum x 0 = 0 := by simp [cum]

lemma cum_of_ge (x : PerishBaseStock.Lifetime.State m) (i : ℕ) (hi : m ≤ i) : cum x i = 0 := by
  unfold cum; rw [dif_neg]; omega

lemma level_of_lt (x : PerishBaseStock.Lifetime.State m) (q : ℝ) (i : ℕ) (hi : i < m) :
    level x q i = cum x i := by simp [level, hi]

lemma level_m (x : PerishBaseStock.Lifetime.State m) (q : ℝ) :
    level x q m = cum x (m - 1) + q := by simp [level]

lemma cum_lifoStep (x : PerishBaseStock.Lifetime.State m) (q d : ℝ) (i : ℕ)
    (h0 : 0 < i) (hi : i < m) :
    cum (lifoStep x q d) i = min (leftover x q d) (level x q (i + 1)) - outdate x q d := by
  unfold cum
  rw [dif_pos ⟨h0, hi⟩]
  simp only [lifoStep]
  congr 3
  omega

/-- `x_{t+1,j-1} + o_t = min{(x_{t,m}-D)⁺, x_{t,j}}` for `1 ≤ j ≤ m`. -/
lemma key (x : PerishBaseStock.Lifetime.State m) (q d q' : ℝ) (j : ℕ) (h1 : 1 ≤ j)
    (hj : j ≤ m) :
    level (lifoStep x q d) q' (j - 1) + outdate x q d = min (leftover x q d) (level x q j) := by
  rw [level_of_lt _ _ _ (by omega)]
  rcases Nat.eq_or_lt_of_le h1 with h | h
  · subst h; simp [cum_zero, outdate]
  · rw [cum_lifoStep _ _ _ _ (by omega) (by omega)]
    have : j - 1 + 1 = j := by omega
    rw [this]; ring

lemma cum_empty (i : ℕ) : cum (PerishBaseStock.Lifetime.emptyState m) i = 0 := by
  unfold cum; split_ifs <;> rfl

/-- Monotone nonnegative cumulative levels. -/
def Inv (x : PerishBaseStock.Lifetime.State m) : Prop :=
  ∀ i j, i ≤ j → j < m → cum x i ≤ cum x j

lemma Inv.nonneg {x : PerishBaseStock.Lifetime.State m} (h : Inv x) (i : ℕ) : 0 ≤ cum x i := by
  by_cases hi : i < m
  · have := h 0 i (Nat.zero_le _) hi; rwa [cum_zero] at this
  · rw [cum_of_ge _ _ (by omega)]

lemma Inv.level_mono {x : PerishBaseStock.Lifetime.State m} (h : Inv x) {q : ℝ} (hq : 0 ≤ q)
    (hm : 1 ≤ m) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) : level x q i ≤ level x q j := by
  rcases Nat.lt_or_ge j m with hjm | hjm
  · rw [level_of_lt _ _ _ hjm, level_of_lt _ _ _ (by omega)]; exact h i j hij hjm
  · have hjm' : j = m := le_antisymm hj hjm
    rw [hjm', level_m]
    rcases Nat.lt_or_ge i m with him | him
    · rw [level_of_lt _ _ _ him]
      have := h i (m - 1) (by omega) (by omega); linarith
    · have : i = m := le_antisymm (hij.trans hj) him
      rw [this, level_m]

lemma Inv.level_nonneg {x : PerishBaseStock.Lifetime.State m} (h : Inv x) {q : ℝ} (hq : 0 ≤ q)
    (i : ℕ) : 0 ≤ level x q i := by
  unfold level; split_ifs
  · exact h.nonneg i
  · linarith [h.nonneg (m - 1)]

lemma Inv.outdate_nonneg {x : PerishBaseStock.Lifetime.State m} (h : Inv x) {q : ℝ}
    (hq : 0 ≤ q) (d : ℝ) : 0 ≤ outdate x q d :=
  le_min (le_max_right _ _) (h.level_nonneg hq 1)

lemma Inv.step {x : PerishBaseStock.Lifetime.State m} (h : Inv x) {q : ℝ} (hq : 0 ≤ q)
    (hm : 1 ≤ m) (d : ℝ) : Inv (lifoStep x q d) := by
  have hmono := fun {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m) => h.level_mono hq hm hij hj
  intro i j hij hj
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    rw [cum_zero]
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0; rw [cum_zero]
    · rw [cum_lifoStep _ _ _ _ hj0 hj, sub_nonneg]
      unfold outdate
      exact min_le_min_left _ (hmono (by omega) (by omega))
  · rw [cum_lifoStep _ _ _ _ hi0 (by omega), cum_lifoStep _ _ _ _ (by omega) hj]
    exact sub_le_sub_right (min_le_min_left _ (hmono (by omega) (by omega))) _

lemma inv_run (π : PerishBaseStock.Lifetime.Policy m) (hm : 1 ≤ m)
    (d : CappedBaseStock.DemandPath) : ∀ t, Inv (run π d t) := by
  intro t
  induction t with
  | zero => intro i j _ _; simp [run, cum_empty]
  | succ t ih => exact ih.step (NNReal.coe_nonneg _) hm _

/-! ### Base-stock specifics -/

lemma bs_upTo (S : ℝ≥0) {x : PerishBaseStock.Lifetime.State m} (h : Inv x)
    (hS : cum x (m - 1) ≤ S) :
    level x ((baseStock m S).φ 0 x : ℝ) m = S := by
  rw [level_m]
  simp only [baseStock]
  rw [Real.coe_toNNReal _ (by linarith)]
  ring

lemma bs_top (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) :
    ∀ t, cum (run (baseStock m S) d t) (m - 1) ≤ S := by
  intro t
  induction t with
  | zero => simp [run, cum_empty]
  | succ t ih =>
    have hinv := inv_run (baseStock m S) hm d t
    rcases Nat.lt_or_ge 1 m with h2 | h1
    · simp only [run]
      rw [cum_lifoStep _ _ _ _ (by omega) (by omega)]
      have hq : (0 : ℝ) ≤ ((baseStock m S).φ t (run (baseStock m S) d t) : ℝ) :=
        NNReal.coe_nonneg _
      have h1 := hinv.outdate_nonneg hq (d t : ℝ)
      have h2 : min (leftover (run (baseStock m S) d t)
          ((baseStock m S).φ t (run (baseStock m S) d t) : ℝ) (d t))
          (level (run (baseStock m S) d t) ((baseStock m S).φ t (run (baseStock m S) d t) : ℝ)
            (m - 1 + 1)) ≤ S := by
        refine (min_le_left _ _).trans ?_
        unfold leftover
        have := bs_upTo S hinv ih
        simp only [baseStock] at this ⊢
        rw [this]
        exact max_le (by linarith [(d t).2]) S.2
      linarith
    · rw [show m - 1 = 0 by omega, cum_zero]; exact S.2

/-- Under `π_S` the order-up-to level is `S` in every period. -/
lemma bs_level_m (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    level (run (baseStock m S) d t) ((baseStock m S).φ t (run (baseStock m S) d t) : ℝ) m = S :=
  bs_upTo S (inv_run _ hm d t) (bs_top S hm d t)

/-- Shorthand for the base-stock outdating and levels. -/
noncomputable abbrev o (m : ℕ) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℝ :=
  outdated (baseStock m S) d t

noncomputable abbrev u (m : ℕ) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t i : ℕ) : ℝ :=
  level (run (baseStock m S) d t) ((baseStock m S).φ t (run (baseStock m S) d t) : ℝ) i

lemma bs_leftover (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    leftover (run (baseStock m S) d t) ((baseStock m S).φ t (run (baseStock m S) d t) : ℝ) (d t)
      = max ((S : ℝ) - d t) 0 := by
  unfold leftover; rw [bs_level_m S hm d t]

/-- One-step recursion `u_{s+1, j-1} = min(L_s, u_{s,j}) - o_s`. -/
lemma u_step (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (s j : ℕ) (h1 : 1 ≤ j)
    (hj : j ≤ m) :
    u m S d (s + 1) (j - 1) = min (max ((S : ℝ) - d s) 0) (u m S d s j) - o m S d s := by
  have := key (run (baseStock m S) d s) ((baseStock m S).φ s (run (baseStock m S) d s) : ℝ)
    (d s) ((baseStock m S).φ (s + 1) (run (baseStock m S) d (s + 1)) : ℝ) j h1 hj
  rw [bs_leftover S hm d s] at this
  simp only [u, o, outdated]
  rw [← this]
  simp [run]

lemma inf'_sub {s : Finset ℕ} (H : s.Nonempty) (f : ℕ → ℝ) (c : ℝ) :
    s.inf' H f - c = s.inf' H (fun i => f i - c) := by
  apply le_antisymm
  · exact Finset.le_inf' _ _ fun i hi => sub_le_sub_right (Finset.inf'_le _ hi) _
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' H f
    rw [he]; exact Finset.inf'_le (fun i => f i - c) hi

lemma inf'_range_succ (k : ℕ) (H1 : (Finset.range (k + 1)).Nonempty)
    (H2 : (Finset.range k).Nonempty) (f : ℕ → ℝ) :
    (Finset.range (k + 1)).inf' H1 f = min (f k) ((Finset.range k).inf' H2 f) := by
  apply le_antisymm
  · exact le_min (Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_self k)))
      (Finset.le_inf' _ _ fun i hi =>
        Finset.inf'_le _ (Finset.mem_range.2 (Nat.lt_succ_of_lt (Finset.mem_range.1 hi))))
  · refine Finset.le_inf' _ _ fun i hi => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Finset.mem_range.1 hi) with h | h
    · exact (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_range.2 h))
    · rw [h]; exact min_le_left _ _

/-- The window formula: for `1 ≤ k ≤ m`,
`u_{t+k, m-k} = min_{i<k} (L_{t+i} - Σ_{j=t+i}^{t+k-1} o_j)`. -/
lemma window (S : ℝ≥0) (hm : 1 ≤ m) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    ∀ k (hk : 1 ≤ k), k ≤ m → u m S d (t + k) (m - k) =
      (Finset.range k).inf' (Finset.nonempty_range_iff.mpr (by omega))
        (fun i => max ((S : ℝ) - d (t + i)) 0 - ∑ j ∈ Finset.Ico (t + i) (t + k), o m S d j) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro _
    have h := u_step S hm d t m hm le_rfl
    simp only [u] at h
    rw [bs_level_m S hm d t, min_eq_left (max_le (by linarith [(d t).2]) (NNReal.coe_nonneg S))] at h
    simp only [u, Finset.range_one, Finset.inf'_singleton, add_zero]
    rw [h, Finset.sum_Ico_succ_top (le_refl t), Finset.Ico_self, Finset.sum_empty, zero_add]
  | succ k hk ih =>
    intro hk1
    have h := u_step S hm d (t + k) (m - k) (by omega) (by omega)
    rw [show m - k - 1 = m - (k + 1) by omega, ih (by omega)] at h
    rw [show t + (k + 1) = t + k + 1 by ring, h]
    rw [inf'_range_succ k _ (Finset.nonempty_range_iff.mpr (by omega)), ← min_sub_sub_right, inf'_sub]
    congr 1
    · rw [Finset.sum_Ico_succ_top (by omega), Finset.Ico_self, Finset.sum_empty, zero_add]
    · refine Finset.inf'_congr _ rfl fun i hi => ?_
      have : t + i ≤ t + k := by have := Finset.mem_range.mp hi; omega
      rw [Finset.sum_Ico_succ_top this]; ring

end L5D

namespace L5D
open PerishBaseStock.Lifo

theorem ec18 (m : ℕ) (hm : 1 ≤ m) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    outdated (baseStock m S) d (t + m - 1) =
      (Finset.range m).inf' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun i => max ((S : ℝ) - d (t + i)) 0 -
          ∑ j ∈ Finset.Ico (t + i) (t + m - 1), outdated (baseStock m S) d j) := by
  have hw := window S hm d t m hm le_rfl
  have h0 : u m S d (t + m) (m - m) = 0 := by
    simp only [u, Nat.sub_self]
    rw [level_of_lt _ _ _ (by omega), cum_zero]
  rw [h0] at hw
  have hsplit : ∀ i ∈ Finset.range m, max ((S : ℝ) - d (t + i)) 0 -
      ∑ j ∈ Finset.Ico (t + i) (t + m), o m S d j =
      (max ((S : ℝ) - d (t + i)) 0 -
        ∑ j ∈ Finset.Ico (t + i) (t + m - 1), outdated (baseStock m S) d j)
        - outdated (baseStock m S) d (t + m - 1) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [show t + m = t + m - 1 + 1 by omega, Finset.sum_Ico_succ_top (by omega)]
    simp only [o, show t + m - 1 + 1 - 1 = t + m - 1 by omega]
    ring
  rw [Finset.inf'_congr _ rfl hsplit, ← inf'_sub] at hw
  linarith

end L5D


open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open LostSalesOrderUpTo.Asymptotic
open PerishBaseStock.Lifo

theorem solution (m : ℕ) (hm : 1 ≤ m) (S : ℝ≥0) (d : CappedBaseStock.DemandPath) (t : ℕ) :
    outdated (baseStock m S) d (t + m - 1) =
      (Finset.range m).inf' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (fun i => max ((S : ℝ) - d (t + i)) 0 -
          ∑ j ∈ Finset.Ico (t + i) (t + m - 1), outdated (baseStock m S) d j) :=
  L5D.ec18 m hm S d t
