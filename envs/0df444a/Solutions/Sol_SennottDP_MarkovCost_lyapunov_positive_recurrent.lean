-- Prove2me | solution 1 for SennottDP.MarkovCost.lyapunov_positive_recurrent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T21:47:09.372986+00:00
-- url     : https://prove2.me/submissions/53590620-8a6b-4bc7-929c-1444572890c7

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain

open scoped ENNReal NNReal
open Filter Topology

set_option autoImplicit false

namespace SennottDP.MarkovCost.LyapP65

open SennottDP.MarkovCost

variable {S : Type} [Countable S]

lemma tsum_snoc {t : ℕ} (F : (Fin (t + 2) → S) → ℝ≥0∞) :
    ∑' y, F y = ∑' x : Fin (t + 1) → S, ∑' k : S, F (Fin.snoc x k) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (t + 2) => S)).tsum_eq]
  exact (ENNReal.tsum_prod (f := fun k x => F (Fin.snoc x k))).trans ENNReal.tsum_comm

lemma pathProb_snoc (M : MC S) {t : ℕ} (x : Fin (t + 1) → S) (k : S) :
    pathProb M (Fin.snoc x k : Fin (t + 2) → S) = pathProb M x * M.P (x (Fin.last t)) k := by
  unfold pathProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun s _ => ?_)
    rw [Fin.succ_castSucc]
    simp only [Fin.snoc_castSucc]
  · rw [Fin.succ_last]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]

lemma snoc_zero' {t : ℕ} (x : Fin (t + 1) → S) (k : S) :
    (Fin.snoc x k : Fin (t + 2) → S) 0 = x 0 := by
  have : (0 : Fin (t + 2)) = Fin.castSucc (0 : Fin (t + 1)) := rfl
  rw [this, Fin.snoc_castSucc]

open Classical in
lemma avoid_zero (M : MC S) (G : Set S) (i k : S) :
    avoidProb M G 0 i k = if k = i then 1 else 0 := by
  unfold avoidProb
  rw [← (Equiv.funUnique (Fin 1) S).symm.tsum_eq]
  by_cases h : k = i
  · subst h
    rw [if_pos rfl, tsum_eq_single k]
    · simp [pathProb]
    · intro a ha
      rw [if_neg]
      simp [ha]
  · rw [if_neg h]
    refine ENNReal.tsum_eq_zero.mpr (fun a => ?_)
    rw [if_neg]
    simp only [Equiv.funUnique_symm_apply, Fin.isValue, not_and]
    intro h1 h2 _
    exact h (by simp_all [uniqueElim])

open Classical in
lemma avoid_succ (M : MC S) (G : Set S) (t : ℕ) (i k : S) :
    avoidProb M G (t + 1) i k =
      if k ∈ G then 0 else ∑' j, avoidProb M G t i j * M.P j k := by
  unfold avoidProb
  rw [tsum_snoc]
  by_cases hk : k ∈ G
  · rw [if_pos hk]
    refine ENNReal.tsum_eq_zero.mpr (fun x => ENNReal.tsum_eq_zero.mpr (fun k' => ?_))
    rw [if_neg]
    rintro ⟨_, h2, h3⟩
    rw [Fin.snoc_last] at h2
    have := h3 (Fin.last (t + 1)) (by simp)
    rw [Fin.snoc_last, h2] at this
    exact this hk
  · rw [if_neg hk]
    have key : ∀ (x : Fin (t + 1) → S) (k' : S),
        (if (Fin.snoc x k' : Fin (t + 2) → S) 0 = i ∧
            (Fin.snoc x k' : Fin (t + 2) → S) (Fin.last (t + 1)) = k ∧
            (∀ s : Fin (t + 2), 0 < s.val → (Fin.snoc x k' : Fin (t + 2) → S) s ∉ G)
          then pathProb M (Fin.snoc x k' : Fin (t + 2) → S) else 0) =
        if k' = k then
          (if x 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → x s ∉ G)
            then pathProb M x * M.P (x (Fin.last t)) k else 0) else 0 := by
      intro x k'
      simp only [snoc_zero', Fin.snoc_last, pathProb_snoc, Fin.forall_fin_succ',
        Fin.snoc_castSucc, Fin.val_castSucc, Fin.val_last]
      by_cases hk' : k' = k
      · subst hk'
        simp only [if_true]
        split_ifs <;> first | rfl | (exfalso; tauto)
      · rw [if_neg hk', if_neg]
        rintro ⟨_, h2, _⟩
        exact hk' h2
    simp_rw [key, tsum_ite_eq]
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun x => ?_)
    rw [tsum_eq_single (x (Fin.last t))]
    · by_cases hc : x 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → x s ∉ G)
      · rw [if_pos hc, if_pos ⟨hc.1, rfl, hc.2⟩]
      · rw [if_neg hc, if_neg, zero_mul]
        rintro ⟨h1, _, h3⟩
        exact hc ⟨h1, h3⟩
    · intro j hj
      rw [if_neg, zero_mul]
      rintro ⟨_, h2, _⟩
      exact hj h2.symm

open Classical in
lemma taboo_succ (M : MC S) (G : Set S) (t : ℕ) (i k : S) :
    taboo M G (t + 1) i k = ∑' j, avoidProb M G t i j * M.P j k := by
  unfold taboo avoidProb
  rw [tsum_snoc]
  have key : ∀ (x : Fin (t + 1) → S) (k' : S),
      (if (Fin.snoc x k' : Fin (t + 2) → S) 0 = i ∧
          (Fin.snoc x k' : Fin (t + 2) → S) (Fin.last (t + 1)) = k ∧
          (∀ s : Fin (t + 2), 0 < s.val → s.val < t + 1 →
            (Fin.snoc x k' : Fin (t + 2) → S) s ∉ G)
        then pathProb M (Fin.snoc x k' : Fin (t + 2) → S) else 0) =
      if k' = k then
        (if x 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → x s ∉ G)
          then pathProb M x * M.P (x (Fin.last t)) k else 0) else 0 := by
    intro x k'
    simp only [snoc_zero', Fin.snoc_last, pathProb_snoc, Fin.forall_fin_succ',
      Fin.snoc_castSucc, Fin.val_castSucc, Fin.val_last, Fin.is_lt, true_implies,
      lt_self_iff_false, false_implies, implies_true, and_true]
    by_cases hk' : k' = k
    · subst hk'
      simp only [if_true]
      split_ifs <;> first | rfl | (exfalso; tauto)
    · rw [if_neg hk', if_neg]
      rintro ⟨_, h2, _⟩
      exact hk' h2
  simp_rw [key, tsum_ite_eq]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr (fun x => ?_)
  rw [tsum_eq_single (x (Fin.last t))]
  · by_cases hc : x 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → x s ∉ G)
    · rw [if_pos hc, if_pos ⟨hc.1, rfl, hc.2⟩]
    · rw [if_neg hc, if_neg, zero_mul]
      rintro ⟨h1, _, h3⟩
      exact hc ⟨h1, h3⟩
  · intro j hj
    rw [if_neg, zero_mul]
    rintro ⟨_, h2, _⟩
    exact hj h2.symm

open Classical in
lemma h_step (M : MC S) (G : Set S) (i : S) (t : ℕ) :
    (∑' k, avoidProb M G (t + 1) i k) + firstPassProb M G i (t + 1) =
      ∑' k, avoidProb M G t i k := by
  have hf : firstPassProb M G i (t + 1) =
      ∑' k, if k ∈ G then ∑' j, avoidProb M G t i j * M.P j k else 0 := by
    unfold firstPassProb
    rw [if_neg (Nat.succ_ne_zero t)]
    refine tsum_congr (fun k => ?_)
    rw [taboo_succ]
  rw [hf, ← ENNReal.tsum_add]
  have hk : ∀ k, avoidProb M G (t + 1) i k +
      (if k ∈ G then ∑' j, avoidProb M G t i j * M.P j k else 0) =
      ∑' j, avoidProb M G t i j * M.P j k := by
    intro k
    rw [avoid_succ]
    split_ifs <;> simp
  rw [tsum_congr hk, ENNReal.tsum_comm]
  refine tsum_congr (fun j => ?_)
  rw [ENNReal.tsum_mul_left, M.P_sum, mul_one]

lemma h_zero (M : MC S) (G : Set S) (i : S) : ∑' k, avoidProb M G 0 i k = 1 := by
  simp_rw [avoid_zero]
  simp

lemma W_zero (M : MC S) (G : Set S) (i : S) (y : S → ℝ≥0) :
    ∑' k, avoidProb M G 0 i k * (y k : ℝ≥0∞) = y i := by
  simp_rw [avoid_zero]
  simp

lemma avoid_ne_zero (M : MC S) (z i j : S) (t : ℕ) (hti : 1 ≤ t ∨ i ≠ z)
    (h : avoidProb M {z} t i j ≠ 0) : j ≠ z := by
  cases t with
  | zero =>
    rw [avoid_zero] at h
    split_ifs at h with hji
    · subst hji
      rcases hti with h1 | h1
      · omega
      · exact h1
    · exact absurd rfl h
  | succ t =>
    rw [avoid_succ] at h
    split_ifs at h with hj
    · exact absurd rfl h
    · simpa using hj

lemma drift (M : MC S) (z : S) (y : S → ℝ≥0) (ε : ℝ≥0)
    (hdrift : ∀ i, i ≠ z → ∑' j, M.P i j * (y j : ℝ≥0∞) + ε ≤ y i) (i : S) (t : ℕ)
    (hti : 1 ≤ t ∨ i ≠ z) :
    ∑' k, avoidProb M {z} (t + 1) i k * (y k : ℝ≥0∞) + (ε : ℝ≥0∞) * ∑' k, avoidProb M {z} t i k
      ≤ ∑' k, avoidProb M {z} t i k * (y k : ℝ≥0∞) := by
  have h1 : ∑' k, avoidProb M {z} (t + 1) i k * (y k : ℝ≥0∞) ≤
      ∑' j, avoidProb M {z} t i j * ∑' k, M.P j k * (y k : ℝ≥0∞) := by
    calc ∑' k, avoidProb M {z} (t + 1) i k * (y k : ℝ≥0∞)
        ≤ ∑' k, (∑' j, avoidProb M {z} t i j * M.P j k) * (y k : ℝ≥0∞) := by
          refine ENNReal.tsum_le_tsum (fun k => ?_)
          rw [avoid_succ]
          split_ifs <;> simp
      _ = ∑' j, avoidProb M {z} t i j * ∑' k, M.P j k * (y k : ℝ≥0∞) := by
          simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
          rw [ENNReal.tsum_comm]
          refine tsum_congr (fun j => tsum_congr (fun k => ?_))
          ring
  calc _ ≤ ∑' j, avoidProb M {z} t i j * ∑' k, M.P j k * (y k : ℝ≥0∞) +
        (ε : ℝ≥0∞) * ∑' k, avoidProb M {z} t i k := add_le_add h1 le_rfl
    _ = ∑' j, avoidProb M {z} t i j * (∑' k, M.P j k * (y k : ℝ≥0∞) + ε) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine tsum_congr (fun j => ?_)
        ring
    _ ≤ _ := by
        refine ENNReal.tsum_le_tsum (fun j => ?_)
        by_cases ha : avoidProb M {z} t i j = 0
        · simp [ha]
        · gcongr
          exact hdrift j (avoid_ne_zero M z i j t hti ha)

lemma tele (W h : ℕ → ℝ≥0∞) (c : ℝ≥0∞) (t0 : ℕ)
    (hs : ∀ t, t0 ≤ t → W (t + 1) + c * h t ≤ W t) :
    ∑' s, c * h (t0 + s) ≤ W t0 := by
  have key : ∀ n, W (t0 + n) + ∑ s ∈ Finset.range n, c * h (t0 + s) ≤ W t0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc t0 n 1]
      calc W (t0 + n + 1) + (∑ s ∈ Finset.range n, c * h (t0 + s) + c * h (t0 + n))
          = (W (t0 + n + 1) + c * h (t0 + n)) + ∑ s ∈ Finset.range n, c * h (t0 + s) := by
            ring
        _ ≤ W (t0 + n) + ∑ s ∈ Finset.range n, c * h (t0 + s) :=
            add_le_add (hs _ (Nat.le_add_right _ _)) le_rfl
        _ ≤ W t0 := ih
  exact ENNReal.tsum_le_of_sum_range_le (fun n => le_trans le_add_self (key n))

lemma abstract_hit (h f : ℕ → ℝ≥0∞) (hstep : ∀ t, h (t + 1) + f (t + 1) = h t)
    (h0 : h 0 = 1) (f0 : f 0 = 0) (hfin : ∑' t, h t ≠ ⊤) :
    ∑' t, f t = 1 ∧ ∑' t, ((t : ℕ) : ℝ≥0∞) * f t ≤ ∑' t, h t := by
  have part : ∀ n, ∑ s ∈ Finset.range (n + 1), f s + h n = 1 := by
    intro n
    induction n with
    | zero => simp [f0, h0]
    | succ n ih => rw [Finset.sum_range_succ, add_assoc, add_comm (f (n + 1)), hstep, ih]
  have hhit : ∑' t, f t = 1 := by
    apply le_antisymm
    · refine ENNReal.tsum_le_of_sum_range_le (fun n => ?_)
      calc ∑ s ∈ Finset.range n, f s ≤ ∑ s ∈ Finset.range (n + 1), f s :=
            Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ n))
        _ ≤ ∑ s ∈ Finset.range (n + 1), f s + h n := le_self_add
        _ = 1 := part n
    · have ht : Tendsto h atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hfin
      have ht2 : Tendsto (fun n => ∑' t, f t + h n) atTop (𝓝 (∑' t, f t + 0)) :=
        tendsto_const_nhds.add ht
      rw [add_zero] at ht2
      refine ge_of_tendsto' ht2 (fun n => ?_)
      rw [← part n]
      exact add_le_add (ENNReal.sum_le_tsum _) le_rfl
  refine ⟨hhit, ?_⟩
  have mid : ∀ n, ∑ s ∈ Finset.range (n + 1), (s : ℝ≥0∞) * f s + n * h n =
      ∑ s ∈ Finset.range n, h s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ (fun s => (s : ℝ≥0∞) * f s) (n + 1), Finset.sum_range_succ h n,
        ← ih, ← hstep n]
      push_cast
      ring
  refine ENNReal.tsum_le_of_sum_range_le (fun n => ?_)
  cases n with
  | zero => simp
  | succ n => exact le_trans le_self_add ((mid n).le.trans (ENNReal.sum_le_tsum _))

lemma hit_mean (M : MC S) (G : Set S) (i : S)
    (hfin : ∑' t, ∑' k, avoidProb M G t i k ≠ ⊤) :
    hitProb M G i = 1 ∧ meanPassage M G i ≤ ∑' t, ∑' k, avoidProb M G t i k := by
  have := abstract_hit (fun t => ∑' k, avoidProb M G t i k) (fun t => firstPassProb M G i t)
    (fun t => h_step M G i t) (h_zero M G i) (by simp [firstPassProb]) hfin
  have hhit : hitProb M G i = 1 := this.1
  refine ⟨hhit, ?_⟩
  unfold meanPassage
  rw [if_pos hhit]
  exact this.2

end SennottDP.MarkovCost.LyapP65

open SennottDP.MarkovCost ENNReal NNReal in
theorem solution {S : Type} [Countable S] (M : MC S) (z : S) (y : S → ℝ≥0)
    (ε : ℝ≥0) (hε : 0 < ε) (hz : ∑' j, M.P z j * (y j : ℝ≥0∞) < ⊤)
    (hdrift : ∀ i, i ≠ z → ∑' j, M.P i j * (y j : ℝ≥0∞) + ε ≤ y i) :
    (∀ i, hitProb M {z} i = 1) ∧
    (∀ i, i ≠ z → meanPassage M {z} i ≤ (y i : ℝ≥0∞) / ε) ∧
    meanPassage M {z} z < ⊤ ∧ PositiveRecurrent M z := by
  have hε0 : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
  have Hne : ∀ i, i ≠ z → ∑' t, ∑' k, avoidProb M {z} t i k ≤ (y i : ℝ≥0∞) / ε := by
    intro i hi
    have := LyapP65.tele (fun t => ∑' k, avoidProb M {z} t i k * (y k : ℝ≥0∞))
      (fun t => ∑' k, avoidProb M {z} t i k) ε 0
      (fun t _ => LyapP65.drift M z y ε hdrift i t (Or.inr hi))
    simp only [zero_add] at this
    rw [ENNReal.tsum_mul_left, LyapP65.W_zero] at this
    rw [ENNReal.le_div_iff_mul_le (Or.inl hε0) (Or.inl ENNReal.coe_ne_top), mul_comm]
    exact this
  have Hz : ∑' t, ∑' k, avoidProb M {z} t z k ≠ ⊤ := by
    have := LyapP65.tele (fun t => ∑' k, avoidProb M {z} t z k * (y k : ℝ≥0∞))
      (fun t => ∑' k, avoidProb M {z} t z k) ε 1
      (fun t ht => LyapP65.drift M z y ε hdrift z t (Or.inl ht))
    rw [ENNReal.tsum_mul_left] at this
    have W1 : ∑' k, avoidProb M {z} 1 z k * (y k : ℝ≥0∞) ≤ ∑' k, M.P z k * (y k : ℝ≥0∞) := by
      refine ENNReal.tsum_le_tsum (fun k => ?_)
      have e := LyapP65.avoid_succ M {z} 0 z k
      simp only [zero_add] at e
      rw [e]
      split_ifs
      · simp
      · simp_rw [LyapP65.avoid_zero]
        simp
    have hlt : (ε : ℝ≥0∞) * ∑' s, ∑' k, avoidProb M {z} (1 + s) z k < ⊤ :=
      lt_of_le_of_lt (this.trans W1) hz
    have hfin : ∑' s, ∑' k, avoidProb M {z} (1 + s) z k ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.mul_top hε0] at hlt
      exact lt_irrefl _ hlt
    have e2 : ∀ s : ℕ, 1 + s = s + 1 := fun s => add_comm 1 s
    simp only [e2] at hfin
    rw [tsum_eq_zero_add' ENNReal.summable, LyapP65.h_zero]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hfin⟩
  have hall : ∀ i, hitProb M {z} i = 1 ∧
      meanPassage M {z} i ≤ ∑' t, ∑' k, avoidProb M {z} t i k := by
    intro i
    apply LyapP65.hit_mean
    by_cases hi : i = z
    · subst hi
      exact Hz
    · exact ne_top_of_le_ne_top (ENNReal.div_lt_top ENNReal.coe_ne_top hε0).ne (Hne i hi)
  have hzlt : meanPassage M {z} z < ⊤ := (hall z).2.trans_lt (lt_top_iff_ne_top.mpr Hz)
  refine ⟨fun i => (hall i).1, fun i hi => (hall i).2.trans (Hne i hi), hzlt, ?_⟩
  unfold PositiveRecurrent
  exact ⟨(hall z).1, hzlt⟩
