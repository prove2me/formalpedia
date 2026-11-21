-- Prove2me | solution 1 for SennottDP.BOR.posRecurrent_in_lowCost
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:43:07.088195+00:00
-- url     : https://prove2.me/submissions/ea7af9eb-022f-414b-8b33-5222903728c3

import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace Aux_BORposRec

open Classical

/-- one-step kernel of the chain induced by a stationary policy -/
noncomputable def Q {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act)
    (e : SennottDP.BOR.StationaryPolicy M) (m l : S) : ℝ≥0∞ :=
  M.P m (e.1 m) l

/-- weight of a state path -/
noncomputable def W {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act)
    (e : SennottDP.BOR.StationaryPolicy M) (x : S) : (n : ℕ) → (Fin (n + 1) → S) → ℝ≥0∞
  | 0, s => if s 0 = x then 1 else 0
  | n + 1, s => W M e x n (Fin.init s) * Q M e (s (Fin.castSucc (Fin.last n))) (s (Fin.last (n + 1)))

/-- n-step transition probabilities -/
noncomputable def a {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act)
    (e : SennottDP.BOR.StationaryPolicy M) (x : S) : ℕ → S → ℝ≥0∞
  | 0, k => if k = x then 1 else 0
  | t + 1, k => ∑' m, a M e x t m * Q M e m k

/-- taboo probabilities: start at `x`, avoid `j` at times `1, …, t` -/
noncomputable def g {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act)
    (e : SennottDP.BOR.StationaryPolicy M) (x j : S) : ℕ → S → ℝ≥0∞
  | 0, k => if k = x then 1 else 0
  | t + 1, k => if k = j then 0 else ∑' m, g M e x j t m * Q M e m k

/-- first passage probabilities -/
noncomputable def f {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act)
    (e : SennottDP.BOR.StationaryPolicy M) (x j : S) : ℕ → ℝ≥0∞
  | 0 => 0
  | t + 1 => ∑' m, g M e x j t m * Q M e m j

/-- probability of no return to `j` within `k` steps -/
noncomputable def r {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act)
    (e : SennottDP.BOR.StationaryPolicy M) (j : S) (k : ℕ) : ℝ≥0∞ :=
  ∑' m, g M e j j k m

theorem tsum_fsum {β : Type} (s : Finset ℕ) (F : ℕ → β → ℝ≥0∞) :
    ∑' b, ∑ x ∈ s, F x b = ∑ x ∈ s, ∑' b, F x b :=
  Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)

theorem dist_eq {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (n : ℕ) (s : Fin (n + 1) → S) (as : Fin n → Act)
    (b : Act) :
    (e.toPolicy).dist n s as b = if b = e.1 (s (Fin.last n)) then 1 else 0 := rfl

theorem histProb_eq {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (x : S) :
    ∀ (n : ℕ) (s : Fin (n + 1) → S) (as : Fin n → Act),
      SennottDP.BOR.histProb e.toPolicy x n s as =
        if as = (fun m => e.1 (s (Fin.castSucc m))) then W M e x n s else 0
  | 0, s, as => by
      have h : as = (fun m => e.1 (s (Fin.castSucc m))) := funext (fun m => m.elim0)
      rw [if_pos h]
      simp only [SennottDP.BOR.histProb, W]
  | n + 1, s, as => by
      rw [SennottDP.BOR.histProb, histProb_eq e x n (Fin.init s) (Fin.init as), dist_eq]
      have key : as = (fun m => e.1 (s (Fin.castSucc m))) ↔
          (Fin.init as = (fun m => e.1 (Fin.init s (Fin.castSucc m))) ∧
            as (Fin.last n) = e.1 (Fin.init s (Fin.last n))) := by
        constructor
        · rintro rfl
          exact ⟨rfl, rfl⟩
        · rintro ⟨h1, h2⟩
          funext m
          rcases Fin.eq_castSucc_or_eq_last m with ⟨m', rfl⟩ | rfl
          · exact congrFun h1 m'
          · exact h2
      by_cases h : as = (fun m => e.1 (s (Fin.castSucc m)))
      · have h' := key.mp h
        rw [if_pos h, if_pos h'.1, if_pos h'.2, h'.2, mul_one] <;> rfl
      · rw [if_neg h]
        by_cases h1 : Fin.init as = (fun m => e.1 (Fin.init s (Fin.castSucc m)))
        · have h2 : ¬ as (Fin.last n) = e.1 (Fin.init s (Fin.last n)) := fun h2 => h (key.mpr ⟨h1, h2⟩)
          rw [if_neg h2, mul_zero, zero_mul]
        · rw [if_neg h1, zero_mul, zero_mul]

theorem tsum_histProb_mul {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (x : S) (n : ℕ) (s : Fin (n + 1) → S) (c : ℝ≥0∞) :
    ∑' as : Fin n → Act, SennottDP.BOR.histProb e.toPolicy x n s as * c = W M e x n s * c := by
  have h : ∀ as : Fin n → Act, SennottDP.BOR.histProb e.toPolicy x n s as * c =
      (if as = (fun m => e.1 (s (Fin.castSucc m))) then W M e x n s else 0) * c := by
    intro as
    rw [histProb_eq]
  rw [tsum_congr h, tsum_eq_single (fun m => e.1 (s (Fin.castSucc m))) (fun b hb => by simp [hb])] <;>
    simp

theorem tsum_ite_histProb {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (x : S) (n : ℕ) (s : Fin (n + 1) → S) (P : Prop)
    {inst : Decidable P} :
    ∑' as : Fin n → Act, @ite _ P inst (SennottDP.BOR.histProb e.toPolicy x n s as) 0 =
      W M e x n s * @ite _ P inst 1 0 := by
  rw [← tsum_histProb_mul e x n s]
  refine tsum_congr (fun as => ?_)
  by_cases h : P
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

theorem stepCost_eq {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (t : ℕ) (s : Fin (t + 1) → S) (as : Fin t → Act) :
    SennottDP.BOR.stepCost e.toPolicy t s as =
      (M.C (s (Fin.last t)) (e.1 (s (Fin.last t))) : ℝ≥0∞) := by
  unfold SennottDP.BOR.stepCost
  rw [Finset.sum_eq_single_of_mem (e.1 (s (Fin.last t))) (e.2 _)
    (fun b _ hb => by simp [dist_eq, hb])]
  simp [dist_eq]

theorem tsum_split {S : Type} {n : ℕ} (F : (Fin (n + 2) → S) → ℝ≥0∞) :
    ∑' s, F s = ∑' s' : Fin (n + 1) → S, ∑' y : S, F (Fin.snoc (α := fun _ => S) s' y) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => S)).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  rfl

theorem W_snoc {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (x : S) (n : ℕ) (s' : Fin (n + 1) → S) (y : S) :
    W M e x (n + 1) (Fin.snoc (α := fun _ => S) s' y) = W M e x n s' * Q M e (s' (Fin.last n)) y := by
  show W M e x n (Fin.init (Fin.snoc (α := fun _ => S) s' y)) *
      Q M e (Fin.snoc (α := fun _ => S) s' y (Fin.castSucc (Fin.last n)))
        (Fin.snoc (α := fun _ => S) s' y (Fin.last (n + 1))) = _
  rw [Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last]

theorem row_sum {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (l : S) : ∑' m, Q M e l m = 1 :=
  M.P_sum l (e.1 l) (e.2 l)

theorem sum_W {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (x : S) : ∀ (t : ℕ) (h : S → ℝ≥0∞),
    ∑' s : Fin (t + 1) → S, W M e x t s * h (s (Fin.last t)) = ∑' k, a M e x t k * h k
  | 0, h => by
      have hL : ∑' s : Fin 1 → S, W M e x 0 s * h (s (Fin.last 0)) = h x := by
        refine (tsum_eq_single (fun _ : Fin 1 => x) (fun s hs => ?_)).trans ?_
        · have hs0 : s 0 ≠ x := fun h0 => hs (funext fun i => by rw [Subsingleton.elim i 0, h0])
          simp [W, hs0]
        · simp [W]
      have hR : ∑' k, a M e x 0 k * h k = h x := by
        refine (tsum_eq_single x (fun k hk => ?_)).trans ?_
        · simp [a, hk]
        · simp [a]
      rw [hL, hR]
  | t + 1, h => by
      rw [tsum_split]
      have h1 : ∀ s' : Fin (t + 1) → S,
          ∑' y : S, W M e x (t + 1) (Fin.snoc (α := fun _ => S) s' y) *
              h (Fin.snoc (α := fun _ => S) s' y (Fin.last (t + 1)))
            = W M e x t s' * ∑' y, Q M e (s' (Fin.last t)) y * h y := by
        intro s'
        simp only [W_snoc, Fin.snoc_last]
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr (fun y => by rw [mul_assoc])
      rw [tsum_congr h1, sum_W e x t (fun m => ∑' y, Q M e m y * h y)]
      calc ∑' k, a M e x t k * ∑' y, Q M e k y * h y
          = ∑' k, ∑' y, a M e x t k * Q M e k y * h y := by
            refine tsum_congr (fun k => ?_)
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr (fun y => by rw [mul_assoc])
        _ = ∑' y, ∑' k, a M e x t k * Q M e k y * h y := ENNReal.tsum_comm
        _ = ∑' y, a M e x (t + 1) y * h y := by
            refine tsum_congr (fun y => ?_)
            rw [ENNReal.tsum_mul_right]
            rfl

theorem stateProb_eq {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (x : S) (t : ℕ) (k : S) :
    SennottDP.BOR.stateProb e.toPolicy x t k = a M e x t k := by
  unfold SennottDP.BOR.stateProb
  have h1 : ∀ s : Fin (t + 1) → S,
      (∑' as : Fin t → Act, if s (Fin.last t) = k then SennottDP.BOR.histProb e.toPolicy x t s as else 0)
        = W M e x t s * (if s (Fin.last t) = k then (1 : ℝ≥0∞) else 0) := by
    intro s
    rw [← tsum_histProb_mul e x t s]
    refine tsum_congr (fun as => ?_)
    by_cases h : s (Fin.last t) = k
    · simp [h]
    · simp [h]
  rw [tsum_congr h1, sum_W e x t (fun m => if m = k then (1 : ℝ≥0∞) else 0)]
  simp

theorem expCost_eq {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (x : S) (t : ℕ) :
    SennottDP.BOR.expCost e.toPolicy x t = ∑' k, a M e x t k * (M.C k (e.1 k) : ℝ≥0∞) := by
  unfold SennottDP.BOR.expCost
  have h1 : ∀ s : Fin (t + 1) → S,
      (∑' as : Fin t → Act, SennottDP.BOR.histProb e.toPolicy x t s as *
          SennottDP.BOR.stepCost e.toPolicy t s as)
        = W M e x t s * (M.C (s (Fin.last t)) (e.1 (s (Fin.last t))) : ℝ≥0∞) := by
    intro s
    rw [← tsum_histProb_mul e x t s]
    refine tsum_congr (fun as => ?_)
    rw [stepCost_eq]
  rw [tsum_congr h1, sum_W e x t (fun k => (M.C k (e.1 k) : ℝ≥0∞))]

theorem a_sum {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (x : S) : ∀ t : ℕ, ∑' k, a M e x t k = 1
  | 0 => by simp [a]
  | t + 1 => by
      calc ∑' k, a M e x (t + 1) k = ∑' k, ∑' m, a M e x t m * Q M e m k := rfl
        _ = ∑' m, ∑' k, a M e x t m * Q M e m k := ENNReal.tsum_comm
        _ = ∑' m, a M e x t m := by
            refine tsum_congr (fun m => ?_)
            rw [ENNReal.tsum_mul_left, row_sum, mul_one]
        _ = 1 := a_sum e x t

theorem cond_snoc {S : Type} (t : ℕ) (j : S) (s' : Fin (t + 1) → S) (y : S) :
    (∀ k : Fin (t + 2), 1 ≤ k.val → Fin.snoc (α := fun _ => S) s' y k ≠ j) ↔
      ((∀ k : Fin (t + 1), 1 ≤ k.val → s' k ≠ j) ∧ y ≠ j) := by
  constructor
  · intro H
    refine ⟨fun k hk => ?_, ?_⟩
    · have := H (Fin.castSucc k) (by simpa using hk)
      simpa using this
    · have := H (Fin.last (t + 1)) (by simp)
      simpa using this
  · rintro ⟨H1, H2⟩ k hk
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
    · simpa using H1 k' (by simpa using hk)
    · simpa using H2

theorem sum_W_taboo {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (x j : S) : ∀ (t : ℕ) (h : S → ℝ≥0∞),
    ∑' s : Fin (t + 1) → S, W M e x t s *
        (if (∀ k : Fin (t + 1), 1 ≤ k.val → s k ≠ j) then h (s (Fin.last t)) else 0)
      = ∑' k, g M e x j t k * h k
  | 0, h => by
      have hc : ∀ s : Fin 1 → S, (∀ k : Fin 1, 1 ≤ k.val → s k ≠ j) := by
        intro s k hk
        have := k.isLt
        omega
      have h1 : ∀ s : Fin 1 → S, W M e x 0 s *
          (if (∀ k : Fin 1, 1 ≤ k.val → s k ≠ j) then h (s (Fin.last 0)) else 0)
            = W M e x 0 s * h (s (Fin.last 0)) := by
        intro s
        rw [if_pos (hc s)]
      rw [tsum_congr h1, sum_W e x 0 h]
      refine tsum_congr (fun k => ?_)
      simp [a, g]
  | t + 1, h => by
      rw [tsum_split]
      have h1 : ∀ s' : Fin (t + 1) → S,
          ∑' y : S, W M e x (t + 1) (Fin.snoc (α := fun _ => S) s' y) *
              (if (∀ k : Fin (t + 2), 1 ≤ k.val → Fin.snoc (α := fun _ => S) s' y k ≠ j) then
                h (Fin.snoc (α := fun _ => S) s' y (Fin.last (t + 1))) else 0)
            = W M e x t s' *
              (if (∀ k : Fin (t + 1), 1 ≤ k.val → s' k ≠ j) then
                ∑' y, Q M e (s' (Fin.last t)) y * (if y ≠ j then h y else 0) else 0) := by
        intro s'
        simp only [W_snoc, Fin.snoc_last, cond_snoc]
        by_cases hc : (∀ k : Fin (t + 1), 1 ≤ k.val → s' k ≠ j)
        · rw [if_pos hc, ← ENNReal.tsum_mul_left]
          refine tsum_congr (fun y => ?_)
          by_cases hy : y = j
          · rw [if_neg (show ¬((∀ k : Fin (t + 1), 1 ≤ k.val → s' k ≠ j) ∧ y ≠ j) from
                fun hh => hh.2 hy), if_neg (show ¬ (y ≠ j) from fun hh => hh hy)]
            simp only [mul_zero]
          · rw [if_pos (show (∀ k : Fin (t + 1), 1 ≤ k.val → s' k ≠ j) ∧ y ≠ j from ⟨hc, hy⟩),
              if_pos hy, mul_assoc]
        · rw [if_neg hc, mul_zero]
          simp [hc]
      rw [tsum_congr h1, sum_W_taboo e x j t (fun m => ∑' y, Q M e m y * (if y ≠ j then h y else 0))]
      calc ∑' k, g M e x j t k * ∑' y, Q M e k y * (if y ≠ j then h y else 0)
          = ∑' k, ∑' y, g M e x j t k * Q M e k y * (if y ≠ j then h y else 0) := by
            refine tsum_congr (fun k => ?_)
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr (fun y => by rw [mul_assoc])
        _ = ∑' y, ∑' k, g M e x j t k * Q M e k y * (if y ≠ j then h y else 0) := ENNReal.tsum_comm
        _ = ∑' y, g M e x j (t + 1) y * h y := by
            refine tsum_congr (fun y => ?_)
            rw [ENNReal.tsum_mul_right]
            show _ = (if y = j then 0 else ∑' m, g M e x j t m * Q M e m y) * h y
            by_cases hy : y = j
            · simp [hy]
            · simp [hy]

theorem cond_snoc2 {S : Type} (t : ℕ) (j : S) (s' : Fin (t + 1) → S) (y : S) :
    ((∀ k : Fin (t + 1 + 1), 1 ≤ k.val → k.val < t + 1 → Fin.snoc (α := fun _ => S) s' y k ∉ ({j} : Set S)) ∧
        Fin.snoc (α := fun _ => S) s' y (Fin.last (t + 1)) ∈ ({j} : Set S) ∧
        Fin.snoc (α := fun _ => S) s' y (Fin.last (t + 1)) = j) ↔
      ((∀ k : Fin (t + 1), 1 ≤ k.val → s' k ≠ j) ∧ y = j) := by
  simp only [Fin.snoc_last, Set.mem_singleton_iff, and_self]
  constructor
  · rintro ⟨H, hy⟩
    refine ⟨fun k hk => ?_, hy⟩
    have := H (Fin.castSucc k) (by simpa using hk) k.isLt
    simpa using this
  · rintro ⟨H1, H2⟩
    refine ⟨fun k hk hk2 => ?_, H2⟩
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
    · simpa using H1 k' (by simpa using hk)
    · simp at hk2

theorem firstPassProb_eq {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (j : S) (t : ℕ) :
    SennottDP.BOR.firstPassProb e.toPolicy j {j} t = f M e j j t := by
  unfold SennottDP.BOR.firstPassProb
  cases t with
  | zero =>
      simp [SennottDP.BOR.firstPassHit, f]
  | succ t =>
      refine (tsum_eq_single j (fun j' hj' => ?_)).trans ?_
      · unfold SennottDP.BOR.firstPassHit
        rw [if_neg (by omega : t + 1 ≠ 0)]
        apply ENNReal.tsum_eq_zero.mpr
        intro s
        apply ENNReal.tsum_eq_zero.mpr
        intro as
        refine if_neg ?_
        rintro ⟨_, h1, h2⟩
        exact hj' (h2.symm.trans (Set.mem_singleton_iff.mp h1))
      · unfold SennottDP.BOR.firstPassHit
        rw [if_neg (by omega : t + 1 ≠ 0)]
        show _ = ∑' m, g M e j j t m * Q M e m j
        simp only [tsum_ite_histProb]
        rw [tsum_split]
        simp only [W_snoc, cond_snoc2]
        have h2 : ∀ s' : Fin (t + 1) → S,
            ∑' y : S, W M e j t s' * Q M e (s' (Fin.last t)) y *
                (if (∀ k : Fin (t + 1), 1 ≤ k.val → s' k ≠ j) ∧ y = j then 1 else 0)
              = W M e j t s' *
                (if (∀ k : Fin (t + 1), 1 ≤ k.val → s' k ≠ j) then
                  Q M e (s' (Fin.last t)) j else 0) := by
          intro s'
          by_cases hc : (∀ k : Fin (t + 1), 1 ≤ k.val → s' k ≠ j)
          · rw [tsum_eq_single j (fun y hy => by simp [hy]),
              if_pos (show (∀ k : Fin (t + 1), 1 ≤ k.val → s' k ≠ j) ∧ j = j from ⟨hc, rfl⟩),
              if_pos hc, mul_one]
          · simp [hc]
        rw [tsum_congr h2, sum_W_taboo e j j t (fun m => Q M e m j)]

theorem r_zero {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (j : S) : r M e j 0 = 1 := by
  simp [r, g]

theorem r_succ {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (j : S) (k : ℕ) :
    r M e j k = f M e j j (k + 1) + r M e j (k + 1) := by
  calc r M e j k = ∑' l, g M e j j k l * ∑' m, Q M e l m := by
        unfold r
        refine tsum_congr (fun l => ?_)
        rw [row_sum, mul_one]
    _ = ∑' l, g M e j j k l * (Q M e l j + ∑' m, ite (m = j) 0 (Q M e l m)) := by
        refine tsum_congr (fun l => ?_)
        rw [ENNReal.tsum_eq_add_tsum_ite (f := Q M e l) j]
    _ = ∑' l, g M e j j k l * Q M e l j +
          ∑' l, ∑' m, ite (m = j) 0 (g M e j j k l * Q M e l m) := by
        rw [← ENNReal.tsum_add]
        refine tsum_congr (fun l => ?_)
        rw [mul_add, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr (fun m => ?_)
        by_cases hm : m = j
        · simp [hm]
        · simp [hm]
    _ = f M e j j (k + 1) + r M e j (k + 1) := by
        rw [ENNReal.tsum_comm]
        have hr : r M e j (k + 1) = ∑' m, ∑' l, ite (m = j) 0 (g M e j j k l * Q M e l m) := by
          unfold r
          refine tsum_congr (fun m => ?_)
          show (if m = j then 0 else ∑' l, g M e j j k l * Q M e l m) = _
          by_cases hm : m = j
          · simp [hm]
          · simp [hm]
        rw [hr]
        rfl

theorem renewal_id {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (j : S) :
    ∀ k : ℕ, r M e j k + ∑ s ∈ Finset.range (k + 1), f M e j j s = 1
  | 0 => by simp [r_zero, f]
  | k + 1 => by
      have ih := renewal_id e j k
      rw [Finset.sum_range_succ, ← ih, r_succ e j k]
      ring

theorem mean_id {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (j : S) :
    ∀ N : ℕ, ∑ t ∈ Finset.range (N + 1), (t : ℝ≥0∞) * f M e j j t + (N : ℝ≥0∞) * r M e j N
      = ∑ k ∈ Finset.range N, r M e j k
  | 0 => by simp
  | N + 1 => by
      have ih := mean_id e j N
      rw [Finset.sum_range_succ (fun t : ℕ => (t : ℝ≥0∞) * f M e j j t) (N + 1),
        Finset.sum_range_succ (fun k => r M e j k) N, ← ih, r_succ e j N]
      push_cast
      ring

theorem lastExit {S Act : Type} [Countable S] {M : SennottDP.Discounted.MDC S Act}
    (e : SennottDP.BOR.StationaryPolicy M) (i j : S) : ∀ (t : ℕ) (k : S),
    ∑ s ∈ Finset.range (t + 1), a M e i s j * g M e j j (t - s) k ≤ a M e i t k
  | 0, k => by
      simp only [zero_add, Finset.sum_range_one, Nat.sub_self]
      by_cases hk : k = j
      · subst hk
        simp [g]
      · have h0 : g M e j j 0 k = 0 := by simp [g, hk]
        rw [h0, mul_zero]
        exact zero_le
  | t + 1, k => by
      rw [Finset.sum_range_succ, Nat.sub_self]
      have hs : ∀ s ∈ Finset.range (t + 1), a M e i s j * g M e j j (t + 1 - s) k =
          a M e i s j * (if k = j then 0 else ∑' m, g M e j j (t - s) m * Q M e m k) := by
        intro s hs
        rw [Finset.mem_range] at hs
        rw [show t + 1 - s = (t - s) + 1 by omega]
        rfl
      rw [Finset.sum_congr rfl hs]
      by_cases hk : k = j
      · subst hk
        simp [g]
      · have h0 : g M e j j 0 k = 0 := by simp [g, hk]
        rw [h0, mul_zero, add_zero]
        simp only [hk, if_false]
        calc ∑ s ∈ Finset.range (t + 1), a M e i s j * ∑' m, g M e j j (t - s) m * Q M e m k
            = ∑' m, (∑ s ∈ Finset.range (t + 1), a M e i s j * g M e j j (t - s) m) * Q M e m k := by
              calc ∑ s ∈ Finset.range (t + 1), a M e i s j * ∑' m, g M e j j (t - s) m * Q M e m k
                  = ∑ s ∈ Finset.range (t + 1), ∑' m, a M e i s j * g M e j j (t - s) m * Q M e m k :=
                    Finset.sum_congr rfl (fun s _ => by
                      rw [← ENNReal.tsum_mul_left]
                      exact tsum_congr (fun m => by rw [mul_assoc]))
                _ = ∑' m, ∑ s ∈ Finset.range (t + 1), a M e i s j * g M e j j (t - s) m * Q M e m k :=
                    (tsum_fsum _ _).symm
                _ = _ := tsum_congr (fun m => by rw [Finset.sum_mul])
          _ ≤ ∑' m, a M e i t m * Q M e m k :=
              ENNReal.tsum_le_tsum (fun m => mul_le_mul_of_nonneg_right (lastExit e i j t m) zero_le)
          _ = a M e i (t + 1) k := rfl

end Aux_BORposRec

open SennottDP.BOR Aux_BORposRec in
theorem solution {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (J : ℝ≥0)
    (hJ : ∀ i, avgValue M i = J) (e : StationaryPolicy M) (he : IsAvgOptimal e.toPolicy)
    (i : S) (ε : ℝ) (hε : 0 < ε) (G : Set S)
    (hG : G = lowCostSetOf M e ((J : ℝ≥0∞) + ENNReal.ofReal ε)) (q : S → ℝ≥0∞)
    (hq : ∀ j ∈ G, Tendsto (fun n => Qavg e.toPolicy n i j) atTop (𝓝 (q j)))
    (h733 : Tendsto (fun n => ∑' j : G, Qavg e.toPolicy n i j) atTop (𝓝 (∑' j : G, q j))) :
    ∃ j ∈ G, PosRecurrent e.toPolicy j ∧ LeadsTo e.toPolicy i j := by
  have hQavg : ∀ n j, Qavg e.toPolicy n i j =
      (∑ t ∈ Finset.range n, a M e i t j) / (n : ℝ≥0∞) := by
    intro n j
    simp only [Qavg, stateProb_eq]
  obtain ⟨K', hK'⟩ : ∃ K' : ℝ≥0∞, K' = (J : ℝ≥0∞) + ENNReal.ofReal ε := ⟨_, rfl⟩
  rw [← hK'] at hG
  have hK'top : K' ≠ ⊤ := by
    rw [hK']
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.ofReal_ne_top⟩
  have hmem : ∀ m, m ∈ G ↔ (M.C m (e.1 m) : ℝ≥0∞) ≤ K' := by
    intro m
    subst hG
    exact Iff.rfl
  have havg : avgCost e.toPolicy i = J := (he i).trans (hJ i)
  -- step 1 : some low-cost state has positive limiting frequency
  have hne : ∑' j : G, q j ≠ 0 := by
    intro hsum0
    rw [hsum0] at h733
    have hpt : ∀ t m, K' * a M e i t m ≤
        K' * G.indicator (a M e i t) m + a M e i t m * (M.C m (e.1 m) : ℝ≥0∞) := by
      intro t m
      by_cases hm : m ∈ G
      · rw [Set.indicator_of_mem hm]
        exact le_self_add
      · rw [Set.indicator_of_notMem hm, mul_zero, zero_add, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        rw [hmem] at hm
        exact le_of_lt (not_le.mp hm)
    have hstep : ∀ t, K' ≤ K' * ∑' m : G, a M e i t m + SennottDP.BOR.expCost e.toPolicy i t := by
      intro t
      rw [expCost_eq, tsum_subtype G (a M e i t)]
      calc K' = K' * ∑' m, a M e i t m := by rw [a_sum, mul_one]
        _ = ∑' m, K' * a M e i t m := ENNReal.tsum_mul_left.symm
        _ ≤ ∑' m, (K' * G.indicator (a M e i t) m + a M e i t m * (M.C m (e.1 m) : ℝ≥0∞)) :=
            ENNReal.tsum_le_tsum (hpt t)
        _ = K' * ∑' m, G.indicator (a M e i t) m + ∑' m, a M e i t m * (M.C m (e.1 m) : ℝ≥0∞) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    have hbound : ∀ n : ℕ, 1 ≤ n → K' ≤ K' * (∑' m : G, Qavg e.toPolicy n i m) +
        SennottDP.BOR.horizonCost e.toPolicy n i / (n : ℝ≥0∞) := by
      intro n hn
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
      have hsum : (n : ℝ≥0∞) * K' ≤ K' * (∑' m : G, ∑ t ∈ Finset.range n, a M e i t m) +
          SennottDP.BOR.horizonCost e.toPolicy n i := by
        unfold SennottDP.BOR.horizonCost
        rw [tsum_fsum, Finset.mul_sum, ← Finset.sum_add_distrib]
        calc (n : ℝ≥0∞) * K' = ∑ t ∈ Finset.range n, K' := by simp
          _ ≤ _ := Finset.sum_le_sum (fun t _ => hstep t)
      have hx : ∑' m : G, Qavg e.toPolicy n i m =
          (∑' m : G, ∑ t ∈ Finset.range n, a M e i t m) * (n : ℝ≥0∞)⁻¹ := by
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr (fun m => ?_)
        rw [hQavg, div_eq_mul_inv]
      rw [hx]
      calc K' = (n : ℝ≥0∞) * K' * (n : ℝ≥0∞)⁻¹ := by
            rw [mul_comm (n : ℝ≥0∞) K', mul_assoc, ENNReal.mul_inv_cancel hn0 hntop, mul_one]
        _ ≤ (K' * (∑' m : G, ∑ t ∈ Finset.range n, a M e i t m) +
              SennottDP.BOR.horizonCost e.toPolicy n i) * (n : ℝ≥0∞)⁻¹ :=
            mul_le_mul_of_nonneg_right hsum zero_le
        _ = _ := by rw [add_mul, mul_assoc, div_eq_mul_inv]
    have hlim0 : Tendsto (fun n : ℕ => K' * ∑' m : G, Qavg e.toPolicy n i m) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul h733 (Or.inr hK'top)
      simpa using this
    have h1 : K' ≤ limsup (fun n : ℕ => K' * (∑' m : G, Qavg e.toPolicy n i m) +
        SennottDP.BOR.horizonCost e.toPolicy n i / (n : ℝ≥0∞)) atTop :=
      le_limsup_of_frequently_le (Filter.Eventually.frequently
        (Filter.eventually_atTop.mpr ⟨1, fun n hn => hbound n hn⟩))
    have h2 : limsup (fun n : ℕ => K' * (∑' m : G, Qavg e.toPolicy n i m) +
        SennottDP.BOR.horizonCost e.toPolicy n i / (n : ℝ≥0∞)) atTop =
        limsup (fun n : ℕ => SennottDP.BOR.horizonCost e.toPolicy n i / (n : ℝ≥0∞)) atTop :=
      ENNReal.limsup_add_of_left_tendsto_zero hlim0 _
    have h3 : limsup (fun n : ℕ => SennottDP.BOR.horizonCost e.toPolicy n i / (n : ℝ≥0∞)) atTop
        = (J : ℝ≥0∞) := havg
    have h4 : K' ≤ (J : ℝ≥0∞) := by
      rw [← h3]
      exact h1.trans (le_of_eq h2)
    have h5 : (J : ℝ≥0∞) < K' := by
      rw [hK']
      exact ENNReal.lt_add_right ENNReal.coe_ne_top (ENNReal.ofReal_pos.mpr hε).ne'
    exact absurd h4 (not_le.mpr h5)
  obtain ⟨⟨j, hjG⟩, hqj⟩ : ∃ j : G, q j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (ENNReal.tsum_eq_zero.mpr hc)
  refine ⟨j, hjG, ?_, ?_⟩
  · -- positive recurrence
    have hqlim := hq j hjG
    have hRK : ∀ K : ℕ, (∑ k ∈ Finset.range K, r M e j k) * q j ≤ 1 := by
      intro K
      have hA : Tendsto (fun n => (∑ k ∈ Finset.range K, r M e j k) * Qavg e.toPolicy n i j)
          atTop (𝓝 ((∑ k ∈ Finset.range K, r M e j k) * q j)) :=
        ENNReal.Tendsto.const_mul hqlim (Or.inl hqj)
      have hB : Tendsto (fun n : ℕ => (1 : ℝ≥0∞) + (K : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) atTop (𝓝 1) := by
        have := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
          (Or.inr (ENNReal.natCast_ne_top K))
        simpa using tendsto_const_nhds.add this
      refine le_of_tendsto_of_tendsto hA hB (Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩)
      have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
      -- the double-sum bound
      have H : ∀ t, ∑ s ∈ Finset.range (t + 1), a M e i s j * r M e j (t - s) ≤ 1 := by
        intro t
        calc ∑ s ∈ Finset.range (t + 1), a M e i s j * r M e j (t - s)
            = ∑ s ∈ Finset.range (t + 1), ∑' m, a M e i s j * g M e j j (t - s) m :=
              Finset.sum_congr rfl (fun s _ => by
                unfold r
                exact ENNReal.tsum_mul_left.symm)
          _ = ∑' m, ∑ s ∈ Finset.range (t + 1), a M e i s j * g M e j j (t - s) m :=
              (tsum_fsum _ _).symm
          _ ≤ ∑' m, a M e i t m := ENNReal.tsum_le_tsum (fun m => lastExit e i j t m)
          _ = 1 := a_sum e i t
      have hswap : ∑ t ∈ Finset.range (n + K), ∑ s ∈ Finset.range (t + 1),
            a M e i s j * r M e j (t - s)
          = ∑ s ∈ Finset.range (n + K), ∑ t ∈ Finset.Ico s (n + K),
            a M e i s j * r M e j (t - s) :=
        Finset.sum_comm' (fun x y => by simp only [Finset.mem_range, Finset.mem_Ico]; omega)
      have hle1 : ∑ t ∈ Finset.range (n + K), ∑ s ∈ Finset.range (t + 1),
            a M e i s j * r M e j (t - s) ≤ ((n + K : ℕ) : ℝ≥0∞) := by
        calc _ ≤ ∑ t ∈ Finset.range (n + K), (1 : ℝ≥0∞) := Finset.sum_le_sum (fun t _ => H t)
          _ = ((n + K : ℕ) : ℝ≥0∞) := by simp
      have hinner : ∀ s ∈ Finset.range n, a M e i s j * ∑ k ∈ Finset.range K, r M e j k ≤
          ∑ t ∈ Finset.Ico s (n + K), a M e i s j * r M e j (t - s) := by
        intro s hs
        rw [Finset.mem_range] at hs
        rw [← Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_sub_cancel_left]
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))) zero_le
      have hcb : (∑ k ∈ Finset.range K, r M e j k) * ∑ s ∈ Finset.range n, a M e i s j ≤
          ((n + K : ℕ) : ℝ≥0∞) := by
        calc (∑ k ∈ Finset.range K, r M e j k) * ∑ s ∈ Finset.range n, a M e i s j
            = ∑ s ∈ Finset.range n, a M e i s j * ∑ k ∈ Finset.range K, r M e j k := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
          _ ≤ ∑ s ∈ Finset.range n, ∑ t ∈ Finset.Ico s (n + K), a M e i s j * r M e j (t - s) :=
              Finset.sum_le_sum hinner
          _ ≤ ∑ s ∈ Finset.range (n + K), ∑ t ∈ Finset.Ico s (n + K),
                a M e i s j * r M e j (t - s) :=
              Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
          _ = _ := hswap.symm
          _ ≤ _ := hle1
      show (∑ k ∈ Finset.range K, r M e j k) * Qavg e.toPolicy n i j ≤
        (1 : ℝ≥0∞) + (K : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹
      rw [hQavg, ← mul_div_assoc]
      calc (∑ k ∈ Finset.range K, r M e j k) * (∑ t ∈ Finset.range n, a M e i t j) / (n : ℝ≥0∞)
          ≤ ((n + K : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞) := ENNReal.div_le_div_right hcb _
        _ = 1 + (K : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ := by
          rw [div_eq_mul_inv, Nat.cast_add, add_mul, ENNReal.mul_inv_cancel hn0 hntop]
    have hrsum : ∑' k, r M e j k ≤ (q j)⁻¹ :=
      ENNReal.tsum_le_of_sum_range_le (fun K => ENNReal.le_inv_iff_mul_le.mpr (hRK K))
    have hrfin : ∑' k, r M e j k ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr hqj) hrsum
    have hr0 : Tendsto (fun k => r M e j k) atTop (𝓝 0) :=
      ENNReal.tendsto_atTop_zero_of_tsum_ne_top hrfin
    have hpart : Tendsto (fun k => ∑ s ∈ Finset.range (k + 1), f M e j j s) atTop
        (𝓝 (∑' s, f M e j j s)) :=
      (ENNReal.tendsto_nat_tsum _).comp (tendsto_add_atTop_nat 1)
    have hsumf : ∑' s, f M e j j s = 1 := by
      have h1 : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 (0 + ∑' s, f M e j j s)) :=
        (hr0.add hpart).congr (renewal_id e j)
      have := tendsto_nhds_unique h1 tendsto_const_nhds
      rw [zero_add] at this
      exact this
    have hfp : ∀ t, SennottDP.BOR.firstPassProb e.toPolicy j {j} t = f M e j j t :=
      firstPassProb_eq e j
    have hhit : SennottDP.BOR.hitProb e.toPolicy j {j} = 1 := by
      unfold SennottDP.BOR.hitProb
      simp only [hfp]
      exact hsumf
    show SennottDP.BOR.hitProb e.toPolicy j {j} = 1 ∧ SennottDP.BOR.meanPassage e.toPolicy j {j} < ⊤
    refine ⟨hhit, ?_⟩
    unfold SennottDP.BOR.meanPassage
    rw [if_pos hhit]
    simp only [hfp]
    have hmean : ∑' t : ℕ, (t : ℝ≥0∞) * f M e j j t ≤ ∑' k, r M e j k := by
      refine ENNReal.tsum_le_of_sum_range_le (fun n => ?_)
      cases n with
      | zero => simp
      | succ N =>
          calc ∑ t ∈ Finset.range (N + 1), (t : ℝ≥0∞) * f M e j j t
              ≤ ∑ t ∈ Finset.range (N + 1), (t : ℝ≥0∞) * f M e j j t + (N : ℝ≥0∞) * r M e j N :=
                le_self_add
            _ = ∑ k ∈ Finset.range N, r M e j k := mean_id e j N
            _ ≤ ∑' k, r M e j k := ENNReal.sum_le_tsum _
    exact lt_of_le_of_lt hmean (lt_top_iff_ne_top.mpr hrfin)
  · -- reachability
    show ∃ t, SennottDP.BOR.stateProb e.toPolicy i t j ≠ 0
    by_contra hc
    push_neg at hc
    have h0 : ∀ t, SennottDP.BOR.stateProb e.toPolicy i t j = 0 := hc
    have hQ : (fun n => Qavg e.toPolicy n i j) = fun _ => 0 := by
      funext n
      simp [Qavg, h0]
    have := hq j hjG
    rw [hQ] at this
    exact hqj (tendsto_nhds_unique this tendsto_const_nhds)
