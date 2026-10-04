-- Prove2me | solution 1 for SennottDP.MarkovCost.lyapunov_passage_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:58:02.39692+00:00
-- url     : https://prove2.me/submissions/a874fe67-1885-42a4-a7c8-b55200f9050e

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.MarkovCost.LPB

variable {S : Type} [Countable S]

theorem lpb_pathProb_snoc (M : MC S) {t : ℕ} (y : Fin (t + 1) → S) (z : S) :
    pathProb M (Fin.snoc y z : Fin (t + 1 + 1) → S) = pathProb M y * M.P (y (Fin.last t)) z := by
  unfold pathProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun s _ => ?_
    rw [Fin.succ_castSucc]
    simp only [Fin.snoc_castSucc]
  · rw [Fin.succ_last]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]

open Classical in
theorem lpb_avoid_zero (M : MC S) (G : Set S) (i k : S) :
    avoidProb M G 0 i k = if i = k then 1 else 0 := by
  classical
  unfold avoidProb
  rw [tsum_eq_single (fun _ => i)]
  · by_cases h : i = k
    · subst h
      rw [if_pos ⟨rfl, rfl, fun s hs => absurd hs (by have := s.2; omega)⟩, if_pos rfl]
      simp [pathProb]
    · rw [if_neg (fun hc => h hc.2.1), if_neg h]
  · intro x hx
    rw [if_neg]
    intro hc
    apply hx
    funext s
    have : s = 0 := Fin.fin_one_eq_zero s
    rw [this, hc.1]

theorem lpb_taboo_succ (M : MC S) (G : Set S) (t : ℕ) (i j : S) :
    taboo M G (t + 1) i j = ∑' k, avoidProb M G t i k * M.P k j := by
  classical
  unfold taboo avoidProb
  rw [← (Fin.snocEquiv (fun _ => S)).tsum_eq]
  refine (ENNReal.tsum_prod (f := fun (z : S) (y : Fin (t + 1) → S) =>
    if (Fin.snocEquiv (fun _ => S) (z, y)) 0 = i ∧
        (Fin.snocEquiv (fun _ => S) (z, y)) (Fin.last (t + 1)) = j ∧
        (∀ s : Fin (t + 1 + 1), 0 < s.val → s.val < t + 1 →
          (Fin.snocEquiv (fun _ => S) (z, y)) s ∉ G)
      then pathProb M (Fin.snocEquiv (fun _ => S) (z, y)) else 0)).trans ?_
  rw [ENNReal.tsum_comm]
  simp_rw [← ENNReal.tsum_mul_right]
  conv_rhs => rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => ?_
  simp only [Fin.snocEquiv_apply]
  rw [tsum_eq_single j, tsum_eq_single (y (Fin.last t))]
  · have h0 : (Fin.snoc y j : Fin (t + 2) → S) 0 = y 0 := by
      show (Fin.snoc y j : Fin (t + 2) → S) (Fin.castSucc 0) = y 0
      rw [Fin.snoc_castSucc]
    have hcond : (∀ s : Fin (t + 1 + 1), 0 < s.val → s.val < t + 1 →
        (Fin.snoc y j : Fin (t + 2) → S) s ∉ G) ↔ (∀ s : Fin (t + 1), 0 < s.val → y s ∉ G) := by
      constructor
      · intro h s hs
        have := h (Fin.castSucc s) (by simpa using hs) (by have := s.2; simp; omega)
        rwa [Fin.snoc_castSucc] at this
      · intro h s hs hst
        have e : s = Fin.castSucc ⟨s.val, hst⟩ := Fin.ext rfl
        rw [e, Fin.snoc_castSucc]
        exact h _ hs
    simp only [lpb_pathProb_snoc, Fin.snoc_last, h0, hcond, true_and, and_true]
    have hp : pathProb M ((Fin.snocEquiv fun _ => S) (j, y)) = pathProb M y * M.P (y (Fin.last t)) j :=
      lpb_pathProb_snoc M y j
    rw [hp]
    split_ifs
    · rfl
    · rw [zero_mul]
  · intro k hk
    rw [if_neg (fun hc => hk hc.2.1.symm), zero_mul]
  · intro z hz
    rw [if_neg (fun hc => hz (by simpa using hc.2.1))]

open Classical in
theorem lpb_avoid_succ (M : MC S) (G : Set S) (t : ℕ) (i j : S) :
    avoidProb M G (t + 1) i j = if j ∈ G then 0 else taboo M G (t + 1) i j := by
  classical
  unfold avoidProb taboo
  split_ifs with hj
  · refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    rw [if_neg]
    rintro ⟨-, hx, hc⟩
    exact hc (Fin.last (t + 1)) (by simp) (hx ▸ hj)
  · refine tsum_congr fun x => ?_
    by_cases hx : x 0 = i ∧ x (Fin.last (t + 1)) = j
    · have e : (∀ s : Fin (t + 1 + 1), 0 < s.val → x s ∉ G) ↔
          (∀ s : Fin (t + 1 + 1), 0 < s.val → s.val < t + 1 → x s ∉ G) := by
        constructor
        · intro h s hs _; exact h s hs
        · intro h s hs
          by_cases hst : s.val < t + 1
          · exact h s hs hst
          · have : s = Fin.last (t + 1) := Fin.ext (by have := s.2; simp; omega)
            rw [this, hx.2]; exact hj
      simp only [hx, true_and, e]
    · rw [if_neg (fun hc => hx ⟨hc.1, hc.2.1⟩), if_neg (fun hc => hx ⟨hc.1, hc.2.1⟩)]

end SennottDP.MarkovCost.LPB

open SennottDP.MarkovCost SennottDP.MarkovCost.LPB in
theorem solution {S : Type} [Countable S] (M : MC S) (G : Set S)
    (hG : G.Nonempty) (y : S → ℝ≥0) (ε : ℝ≥0) (hε : 0 < ε)
    (hdrift : ∀ i ∉ G, ∑' j, M.P i j * (y j : ℝ≥0∞) + ε ≤ y i) :
    ∀ i ∉ G, hitProb M G i = 1 ∧ meanPassage M G i ≤ (y i : ℝ≥0∞) / ε := by
  classical
  intro i hi
  set a : ℕ → ℝ≥0∞ := fun t => ∑' k, avoidProb M G t i k with ha
  set f : ℕ → ℝ≥0∞ := fun t => firstPassProb M G i t with hf
  -- states reachable while avoiding `G` lie outside `G`
  have hkG : ∀ t k, avoidProb M G t i k ≠ 0 → k ∉ G := by
    intro t k hk
    cases t with
    | zero =>
      rw [lpb_avoid_zero] at hk
      split_ifs at hk with h
      · exact h ▸ hi
      · exact absurd rfl hk
    | succ t =>
      rw [lpb_avoid_succ] at hk
      split_ifs at hk with h
      · exact absurd rfl hk
      · exact h
  have ha0 : a 0 = 1 := by
    simp only [ha, lpb_avoid_zero]
    rw [tsum_eq_single i (fun k hk => if_neg (Ne.symm hk)), if_pos rfl]
  have htaboo_sum : ∀ t, ∑' k, taboo M G (t + 1) i k = a t := by
    intro t
    simp only [lpb_taboo_succ]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, M.P_sum, mul_one]
    rfl
  have hstep : ∀ t, a t = a (t + 1) + f (t + 1) := by
    intro t
    rw [← htaboo_sum t]
    simp only [ha, hf, firstPassProb, lpb_avoid_succ, Nat.succ_ne_zero, if_false]
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun k => ?_
    split_ifs <;> simp
  -- the drift inequality along the taboo chain
  set Y : ℕ → ℝ≥0∞ := fun t => ∑' k, avoidProb M G t i k * (y k : ℝ≥0∞) with hY
  have hYstep : ∀ t, Y (t + 1) + ε * a t ≤ Y t := by
    intro t
    have h1 : Y (t + 1) ≤ ∑' k, avoidProb M G t i k * ∑' j, M.P k j * (y j : ℝ≥0∞) := by
      calc Y (t + 1) ≤ ∑' j, taboo M G (t + 1) i j * (y j : ℝ≥0∞) := by
            refine ENNReal.tsum_le_tsum fun j => ?_
            rw [lpb_avoid_succ]
            split_ifs <;> simp
        _ = ∑' k, avoidProb M G t i k * ∑' j, M.P k j * (y j : ℝ≥0∞) := by
            simp only [lpb_taboo_succ, ← ENNReal.tsum_mul_right]
            rw [ENNReal.tsum_comm]
            refine tsum_congr fun k => ?_
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun j => by ring
    calc Y (t + 1) + ε * a t
        ≤ ∑' k, avoidProb M G t i k * ∑' j, M.P k j * (y j : ℝ≥0∞) + ε * a t := by gcongr
      _ = ∑' k, avoidProb M G t i k * (∑' j, M.P k j * (y j : ℝ≥0∞) + ε) := by
          rw [ha, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
          exact tsum_congr fun k => by ring
      _ ≤ Y t := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          by_cases hk : avoidProb M G t i k = 0
          · simp [hk]
          · exact mul_le_mul_of_nonneg_left (hdrift k (hkG t k hk)) bot_le
  have hY0 : Y 0 = y i := by
    simp only [hY, lpb_avoid_zero]
    rw [tsum_eq_single i (fun k hk => by rw [if_neg (Ne.symm hk), zero_mul]), if_pos rfl, one_mul]
  have htel : ∀ n, Y n + ε * ∑ t ∈ Finset.range n, a t ≤ y i := by
    intro n
    induction n with
    | zero => simp [hY0]
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add]
      calc Y (n + 1) + (ε * ∑ t ∈ Finset.range n, a t + ε * a n)
          = (Y (n + 1) + ε * a n) + ε * ∑ t ∈ Finset.range n, a t := by ring
        _ ≤ Y n + ε * ∑ t ∈ Finset.range n, a t := by gcongr; exact hYstep n
        _ ≤ y i := ih
  have hεne : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast hε.ne'
  have hsum_a : ∑' t, a t ≤ (y i : ℝ≥0∞) / ε := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hεne) (Or.inl ENNReal.coe_ne_top), mul_comm]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
    rw [← Finset.mul_sum]
    exact le_trans le_add_self (htel n)
  have hsum_fin : ∑' t, a t ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.coe_ne_top hεne) hsum_a
  have ha_lim : Tendsto a atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum_fin
  -- partial sums of the first passage law
  have hf0 : f 0 = 0 := by simp [hf, firstPassProb]
  have hpart : ∀ n, ∑ t ∈ Finset.range (n + 1), f t + a n = 1 := by
    intro n
    induction n with
    | zero => simp [hf0, ha0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, hstep n]
      ring
  have ha_le : ∀ n, a n ≤ 1 := fun n => by rw [← hpart n]; exact le_add_self
  have hhit : hitProb M G i = 1 := by
    have h1 : Tendsto (fun n => ∑ t ∈ Finset.range (n + 1), f t) atTop (𝓝 (hitProb M G i)) :=
      (ENNReal.tendsto_nat_tsum f).comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun n => ∑ t ∈ Finset.range (n + 1), f t) atTop (𝓝 1) := by
      have e : ∀ n, ∑ t ∈ Finset.range (n + 1), f t = 1 - a n := fun n =>
        ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (ha_le n)) (hpart n)
      simp_rw [e]
      have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) ha_lim
        (Or.inl ENNReal.one_ne_top)
      simpa using this
    exact tendsto_nhds_unique h1 h2
  refine ⟨hhit, ?_⟩
  -- the tail-sum bound for the mean passage time
  have htail : ∀ s m, ∑ t ∈ Finset.range (s + 1 + m), (if s < t then f t else 0) + a (s + m) = a s := by
    intro s m
    induction m with
    | zero =>
      rw [add_zero, add_zero]
      have : ∑ t ∈ Finset.range (s + 1), (if s < t then f t else 0) = 0 :=
        Finset.sum_eq_zero fun t ht => if_neg (by have := Finset.mem_range.mp ht; omega)
      rw [this, zero_add]
    | succ m ih =>
      have e1 : s + 1 + (m + 1) = (s + 1 + m) + 1 := by omega
      have e2 : s + (m + 1) = (s + m) + 1 := by omega
      rw [e1, e2, Finset.sum_range_succ, if_pos (by omega), ← ih, hstep (s + m)]
      rw [show s + 1 + m = s + m + 1 by omega]
      ring
  have htail_le : ∀ s, ∑' t, (if s < t then f t else 0) ≤ a s := by
    intro s
    refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
    rcases le_or_gt n (s + 1) with hn | hn
    · have : ∑ t ∈ Finset.range n, (if s < t then f t else 0) = 0 :=
        Finset.sum_eq_zero fun t ht => if_neg (by have := Finset.mem_range.mp ht; omega)
      rw [this]; exact bot_le
    · obtain ⟨m, rfl⟩ : ∃ m, n = s + 1 + m := ⟨n - (s + 1), by omega⟩
      rw [← htail s m]
      exact le_self_add
  have hmean : ∑' t : ℕ, (t : ℝ≥0∞) * f t = ∑' s, ∑' t, (if s < t then f t else 0) := by
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun t => ?_
    rw [tsum_eq_sum (s := Finset.range t) (fun s hs => if_neg (fun h => hs (Finset.mem_range.mpr h)))]
    rw [Finset.sum_congr rfl (fun s hs => if_pos (Finset.mem_range.mp hs)), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  unfold meanPassage
  rw [if_pos hhit]
  show ∑' t : ℕ, (t : ℝ≥0∞) * f t ≤ _
  rw [hmean]
  exact (ENNReal.tsum_le_tsum htail_le).trans hsum_a


