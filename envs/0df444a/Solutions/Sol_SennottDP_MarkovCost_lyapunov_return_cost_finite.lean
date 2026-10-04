-- Prove2me | solution 1 for SennottDP.MarkovCost.lyapunov_return_cost_finite
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T20:07:02.993906+00:00
-- url     : https://prove2.me/submissions/a2a5b011-75fe-400f-8d65-a5d3062ee439

import Mathlib
import Definitions.Def_SennottDP_MarkovCost_Chain
import Definitions.Def_SennottDP_MarkovCost_Costs

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


/-- Accumulated cost (before time `t`) on surviving paths ending at `k`. -/
noncomputable def lpbW (M : MC S) (C : S → ℝ≥0) (G : Set S) (t : ℕ) (i k : S) : ℝ≥0∞ := by
  classical
  exact ∑' x : Fin (t + 1) → S,
    if x 0 = i ∧ x (Fin.last t) = k ∧ (∀ s : Fin (t + 1), 0 < s.val → x s ∉ G)
    then pathProb M x * ∑ s : Fin t, (C (x s.castSucc) : ℝ≥0∞) else 0

/-- The `t`-th summand of `passageCost`. -/
noncomputable def lpbG (M : MC S) (C : S → ℝ≥0) (G : Set S) (t : ℕ) (i : S) : ℝ≥0∞ := by
  classical
  exact ∑' x : Fin (t + 1) → S,
    if t ≠ 0 ∧ x 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → s.val < t → x s ∉ G) ∧
        x (Fin.last t) ∈ G
    then pathProb M x * ∑ s : Fin t, (C (x s.castSucc) : ℝ≥0∞) else 0

theorem lpb_cost_snoc (C : S → ℝ≥0) {t : ℕ} (y : Fin (t + 1) → S) (z : S) :
    ∑ s : Fin (t + 1), (C ((Fin.snoc y z : Fin (t + 1 + 1) → S) s.castSucc) : ℝ≥0∞) =
      ∑ s : Fin t, (C (y s.castSucc) : ℝ≥0∞) + C (y (Fin.last t)) := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc]

theorem lpb_W_zero (M : MC S) (C : S → ℝ≥0) (G : Set S) (i k : S) : lpbW M C G 0 i k = 0 := by
  unfold lpbW
  simp

theorem lpb_snoc_avoid {G : Set S} {t : ℕ} (y : Fin (t + 1) → S) (z : S) :
    (∀ s : Fin (t + 1 + 1), 0 < s.val → (Fin.snoc y z : Fin (t + 1 + 1) → S) s ∉ G) ↔
      ((∀ s : Fin (t + 1), 0 < s.val → y s ∉ G) ∧ z ∉ G) := by
  constructor
  · intro h
    refine ⟨fun s hs => ?_, ?_⟩
    · have := h (Fin.castSucc s) (by simpa using hs)
      rwa [Fin.snoc_castSucc] at this
    · have := h (Fin.last (t + 1)) (by simp)
      rwa [Fin.snoc_last] at this
  · rintro ⟨h, hz⟩ s hs
    refine Fin.lastCases (fun _ => ?_) (fun s' hs' => ?_) s hs
    · rw [Fin.snoc_last]; exact hz
    · rw [Fin.snoc_castSucc]; exact h s' (by simpa using hs')

theorem lpb_snoc_taboo {G : Set S} {t : ℕ} (y : Fin (t + 1) → S) (z : S) :
    (∀ s : Fin (t + 1 + 1), 0 < s.val → s.val < t + 1 →
        (Fin.snoc y z : Fin (t + 1 + 1) → S) s ∉ G) ↔
      (∀ s : Fin (t + 1), 0 < s.val → y s ∉ G) := by
  constructor
  · intro h s hs
    have := h (Fin.castSucc s) (by simpa using hs) (by have := s.2; simp; omega)
    rwa [Fin.snoc_castSucc] at this
  · intro h s hs hst
    have e : s = Fin.castSucc ⟨s.val, hst⟩ := Fin.ext rfl
    rw [e, Fin.snoc_castSucc]
    exact h _ hs

theorem lpb_snoc_zero {t : ℕ} (y : Fin (t + 1) → S) (z : S) :
    (Fin.snoc y z : Fin (t + 1 + 1) → S) 0 = y 0 := by
  show (Fin.snoc y z : Fin (t + 1 + 1) → S) (Fin.castSucc 0) = y 0
  rw [Fin.snoc_castSucc]

open Classical in
/-- The per-path quantity: surviving path `y` weighted by its probability and its cost up to and
including time `t`. -/
noncomputable def lpbQ (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) {t : ℕ}
    (y : Fin (t + 1) → S) : ℝ≥0∞ :=
  if y 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → y s ∉ G) then
    pathProb M y * (∑ s : Fin t, (C (y s.castSucc) : ℝ≥0∞) + C (y (Fin.last t))) else 0

open Classical in
theorem lpb_W_succ_eq (M : MC S) (C : S → ℝ≥0) (G : Set S) (t : ℕ) (i j : S) :
    lpbW M C G (t + 1) i j =
      ∑' y : Fin (t + 1) → S, (if j ∈ G then 0 else lpbQ M C G i y * M.P (y (Fin.last t)) j) := by
  unfold lpbW
  rw [← (Fin.snocEquiv (fun _ => S)).tsum_eq]
  refine (ENNReal.tsum_prod (f := fun (z : S) (y : Fin (t + 1) → S) =>
    if (Fin.snocEquiv (fun _ => S) (z, y)) 0 = i ∧
        (Fin.snocEquiv (fun _ => S) (z, y)) (Fin.last (t + 1)) = j ∧
        (∀ s : Fin (t + 1 + 1), 0 < s.val → (Fin.snocEquiv (fun _ => S) (z, y)) s ∉ G)
      then pathProb M (Fin.snocEquiv (fun _ => S) (z, y)) *
        ∑ s : Fin (t + 1), (C ((Fin.snocEquiv (fun _ => S) (z, y)) s.castSucc) : ℝ≥0∞)
      else 0)).trans ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => ?_
  simp only [Fin.snocEquiv_apply]
  rw [tsum_eq_single j]
  · have hp : pathProb M ((Fin.snocEquiv fun _ => S) (j, y)) =
        pathProb M y * M.P (y (Fin.last t)) j := lpb_pathProb_snoc M y j
    simp only [lpb_cost_snoc, hp, lpb_snoc_zero, Fin.snoc_last, lpb_snoc_avoid]
    unfold lpbQ
    by_cases hj : j ∈ G
    · rw [if_pos hj, if_neg (fun hc => hc.2.2.2 hj)]
    · rw [if_neg hj]
      by_cases hy : y 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → y s ∉ G)
      · rw [if_pos ⟨hy.1, trivial, hy.2, hj⟩, if_pos hy]; ring
      · rw [if_neg (fun hc => hy ⟨hc.1, hc.2.2.1⟩), if_neg hy, zero_mul]
  · intro z hz
    rw [if_neg (fun hc => hz (by simpa using hc.2.1))]

open Classical in
theorem lpb_G_succ_eq (M : MC S) (C : S → ℝ≥0) (G : Set S) (t : ℕ) (i : S) :
    lpbG M C G (t + 1) i =
      ∑' y : Fin (t + 1) → S, lpbQ M C G i y * ∑' z, (if z ∈ G then M.P (y (Fin.last t)) z else 0) := by
  unfold lpbG
  rw [← (Fin.snocEquiv (fun _ => S)).tsum_eq]
  refine (ENNReal.tsum_prod (f := fun (z : S) (y : Fin (t + 1) → S) =>
    if t + 1 ≠ 0 ∧ (Fin.snocEquiv (fun _ => S) (z, y)) 0 = i ∧
        (∀ s : Fin (t + 1 + 1), 0 < s.val → s.val < t + 1 →
          (Fin.snocEquiv (fun _ => S) (z, y)) s ∉ G) ∧
        (Fin.snocEquiv (fun _ => S) (z, y)) (Fin.last (t + 1)) ∈ G
      then pathProb M (Fin.snocEquiv (fun _ => S) (z, y)) *
        ∑ s : Fin (t + 1), (C ((Fin.snocEquiv (fun _ => S) (z, y)) s.castSucc) : ℝ≥0∞)
      else 0)).trans ?_
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun y => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun z => ?_
  simp only [Fin.snocEquiv_apply]
  have hp : pathProb M ((Fin.snocEquiv fun _ => S) (z, y)) =
      pathProb M y * M.P (y (Fin.last t)) z := lpb_pathProb_snoc M y z
  simp only [lpb_cost_snoc, hp, lpb_snoc_zero, Fin.snoc_last, lpb_snoc_taboo]
  unfold lpbQ
  by_cases hz : z ∈ G
  · rw [if_pos hz]
    by_cases hy : y 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → y s ∉ G)
    · rw [if_pos ⟨by omega, hy.1, hy.2, hz⟩, if_pos hy]; ring
    · rw [if_neg (fun hc => hy ⟨hc.2.1, hc.2.2.1⟩), if_neg hy, zero_mul]
  · rw [if_neg hz, if_neg (fun hc => hz hc.2.2.2), mul_zero]

open Classical in
theorem lpb_W_avoid_eq (M : MC S) (C : S → ℝ≥0) (G : Set S) (t : ℕ) (i : S) :
    ∑' k, (lpbW M C G t i k + avoidProb M G t i k * (C k : ℝ≥0∞)) =
      ∑' y : Fin (t + 1) → S, lpbQ M C G i y := by
  unfold lpbW avoidProb
  have e : ∀ k, (∑' x : Fin (t + 1) → S,
        (if x 0 = i ∧ x (Fin.last t) = k ∧ (∀ s : Fin (t + 1), 0 < s.val → x s ∉ G)
          then pathProb M x * ∑ s : Fin t, (C (x s.castSucc) : ℝ≥0∞) else 0)) +
      (∑' x : Fin (t + 1) → S,
        (if x 0 = i ∧ x (Fin.last t) = k ∧ (∀ s : Fin (t + 1), 0 < s.val → x s ∉ G)
          then pathProb M x else 0)) * (C k : ℝ≥0∞) =
      ∑' x : Fin (t + 1) → S, (if x (Fin.last t) = k then lpbQ M C G i x else 0) := by
    intro k
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
    refine tsum_congr fun x => ?_
    unfold lpbQ
    by_cases hk : x (Fin.last t) = k
    · rw [if_pos hk]
      by_cases hx : x 0 = i ∧ (∀ s : Fin (t + 1), 0 < s.val → x s ∉ G)
      · rw [if_pos ⟨hx.1, hk, hx.2⟩, if_pos ⟨hx.1, hk, hx.2⟩, if_pos hx, hk]; ring
      · rw [if_neg (fun hc => hx ⟨hc.1, hc.2.2⟩), if_neg (fun hc => hx ⟨hc.1, hc.2.2⟩), if_neg hx]
        simp
    · rw [if_neg (fun hc => hk hc.2.1), if_neg (fun hc => hk hc.2.1), if_neg hk]
      simp
  rw [tsum_congr e, ENNReal.tsum_comm]
  refine tsum_congr fun x => ?_
  rw [tsum_eq_single (x (Fin.last t)) (fun k hk => if_neg (Ne.symm hk)), if_pos rfl]

theorem lpb_W_succ (M : MC S) (C : S → ℝ≥0) (G : Set S) (t : ℕ) (i : S) :
    ∑' j, lpbW M C G (t + 1) i j + lpbG M C G (t + 1) i =
      ∑' k, (lpbW M C G t i k + avoidProb M G t i k * (C k : ℝ≥0∞)) := by
  classical
  rw [lpb_W_avoid_eq, lpb_G_succ_eq]
  simp only [lpb_W_succ_eq]
  rw [ENNReal.tsum_comm, ← ENNReal.tsum_add]
  refine tsum_congr fun y => ?_
  have hsplit : ∑' j, (if j ∈ G then 0 else lpbQ M C G i y * M.P (y (Fin.last t)) j) +
      lpbQ M C G i y * ∑' z, (if z ∈ G then M.P (y (Fin.last t)) z else 0) =
      lpbQ M C G i y * ∑' z, M.P (y (Fin.last t)) z := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    split_ifs <;> simp
  rw [hsplit, M.P_sum, mul_one]

theorem lpb_reach (M : MC S) (G : Set S) (i : S) (hi : i ∉ G) :
    ∀ t k, avoidProb M G t i k ≠ 0 → k ∉ G := by
  classical
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

/-- General Lyapunov bound for the expected first passage cost. -/
theorem lpb_cost_bound (M : MC S) (C : S → ℝ≥0) (G : Set S) (i : S) (r : S → ℝ≥0) (F : ℝ≥0)
    (hb : ∀ t k, avoidProb M G t i k ≠ 0 → ∑' j, M.P k j * (r j : ℝ≥0∞) + C k ≤ r k + F)
    (hm : meanPassage M G i < ⊤) :
    passageCost M C G i ≤ r i + F * meanPassage M G i := by
  classical
  set a : ℕ → ℝ≥0∞ := fun t => ∑' k, avoidProb M G t i k with ha
  set f : ℕ → ℝ≥0∞ := fun t => firstPassProb M G i t with hf
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
  have hf0 : f 0 = 0 := by simp [hf, firstPassProb]
  have hpart : ∀ n, ∑ t ∈ Finset.range (n + 1), f t + a n = 1 := by
    intro n
    induction n with
    | zero => simp [hf0, ha0]
    | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, hstep n]
      ring
  have hhit : hitProb M G i = 1 := by
    by_contra h
    unfold meanPassage at hm
    rw [if_neg h] at hm
    exact lt_irrefl _ hm
  have ha_lim : Tendsto a atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ∑ t ∈ Finset.range (n + 1), f t) atTop (𝓝 1) := by
      rw [← hhit]
      exact (ENNReal.tendsto_nat_tsum f).comp (tendsto_add_atTop_nat 1)
    have e : ∀ n, a n = 1 - ∑ t ∈ Finset.range (n + 1), f t := by
      intro n
      have hle : ∑ t ∈ Finset.range (n + 1), f t ≤ 1 := by rw [← hpart n]; exact le_self_add
      exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
        (by rw [add_comm]; exact hpart n)
    have hae : a = fun n => 1 - ∑ t ∈ Finset.range (n + 1), f t := funext e
    rw [hae]
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) h1 (Or.inl ENNReal.one_ne_top)
    simpa using this
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
  have htail_eq : ∀ s, ∑' t, (if s < t then f t else 0) = a s := by
    intro s
    set g : ℕ → ℝ≥0∞ := fun t => if s < t then f t else 0 with hg
    have hk1 : Tendsto (fun m : ℕ => s + 1 + m) atTop atTop := by
      simpa [add_comm] using tendsto_add_atTop_nat (s + 1)
    have hk2 : Tendsto (fun m : ℕ => s + m) atTop atTop := by
      simpa [add_comm] using tendsto_add_atTop_nat s
    have hA : Tendsto (fun m : ℕ => ∑ t ∈ Finset.range (s + 1 + m), g t) atTop (𝓝 (∑' t, g t)) :=
      (ENNReal.tendsto_nat_tsum g).comp hk1
    have hB : Tendsto (fun m : ℕ => a (s + m)) atTop (𝓝 0) := ha_lim.comp hk2
    have h1 := hA.add hB
    rw [add_zero] at h1
    have h2 : (fun m : ℕ => ∑ t ∈ Finset.range (s + 1 + m), g t + a (s + m)) = fun _ => a s :=
      funext fun m => htail s m
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hmean : meanPassage M G i = ∑' s, a s := by
    unfold meanPassage
    rw [if_pos hhit]
    show ∑' t : ℕ, (t : ℝ≥0∞) * f t = _
    simp_rw [← htail_eq]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun t => ?_
    rw [tsum_eq_sum (s := Finset.range t) (fun s hs => if_neg (fun h => hs (Finset.mem_range.mpr h)))]
    rw [Finset.sum_congr rfl (fun s hs => if_pos (Finset.mem_range.mp hs)), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  -- the cost recursion
  set c : ℕ → ℝ≥0∞ := fun t => ∑' k, avoidProb M G t i k * (C k : ℝ≥0∞) with hc
  set V : ℕ → ℝ≥0∞ := fun t => ∑' k, lpbW M C G t i k with hV
  have hV0 : V 0 = 0 := by simp [hV, lpb_W_zero]
  have hg0 : lpbG M C G 0 i = 0 := by unfold lpbG; simp
  have hVstep : ∀ t, V (t + 1) + lpbG M C G (t + 1) i = V t + c t := by
    intro t
    rw [hV, hc]
    simp only
    rw [lpb_W_succ, ENNReal.tsum_add]
  have hgpart : ∀ n, ∑ t ∈ Finset.range (n + 1), lpbG M C G t i + V n = ∑ t ∈ Finset.range n, c t := by
    intro n
    induction n with
    | zero => simp [hg0, hV0]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun t => c t), ← ih, add_assoc,
        add_comm (lpbG M C G (n + 1) i), hVstep n]
      ring
  have hcost : passageCost M C G i = ∑' t, lpbG M C G t i := rfl
  -- the drift along the chain
  set Y : ℕ → ℝ≥0∞ := fun t => ∑' k, avoidProb M G t i k * (r k : ℝ≥0∞) with hY
  have hYstep : ∀ t, Y (t + 1) + c t ≤ Y t + F * a t := by
    intro t
    have h1 : Y (t + 1) ≤ ∑' k, avoidProb M G t i k * ∑' j, M.P k j * (r j : ℝ≥0∞) := by
      calc Y (t + 1) ≤ ∑' j, taboo M G (t + 1) i j * (r j : ℝ≥0∞) := by
            refine ENNReal.tsum_le_tsum fun j => ?_
            rw [lpb_avoid_succ]
            split_ifs <;> simp
        _ = ∑' k, avoidProb M G t i k * ∑' j, M.P k j * (r j : ℝ≥0∞) := by
            simp only [lpb_taboo_succ, ← ENNReal.tsum_mul_right]
            rw [ENNReal.tsum_comm]
            refine tsum_congr fun k => ?_
            rw [← ENNReal.tsum_mul_left]
            exact tsum_congr fun j => by ring
    calc Y (t + 1) + c t
        ≤ ∑' k, avoidProb M G t i k * ∑' j, M.P k j * (r j : ℝ≥0∞) + c t := by gcongr
      _ = ∑' k, avoidProb M G t i k * (∑' j, M.P k j * (r j : ℝ≥0∞) + C k) := by
          rw [hc, ← ENNReal.tsum_add]
          exact tsum_congr fun k => by ring
      _ ≤ ∑' k, avoidProb M G t i k * ((r k : ℝ≥0∞) + F) := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          by_cases hk : avoidProb M G t i k = 0
          · simp [hk]
          · exact mul_le_mul_of_nonneg_left (hb t k hk) bot_le
      _ = Y t + F * a t := by
          rw [hY, ha, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
          exact tsum_congr fun k => by ring
  have hY0 : Y 0 = r i := by
    simp only [hY, lpb_avoid_zero]
    rw [tsum_eq_single i (fun k hk => by rw [if_neg (Ne.symm hk), zero_mul]), if_pos rfl, one_mul]
  have htel : ∀ n, Y n + ∑ t ∈ Finset.range n, c t ≤ r i + F * ∑ t ∈ Finset.range n, a t := by
    intro n
    induction n with
    | zero => simp [hY0]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
      calc Y (n + 1) + (∑ t ∈ Finset.range n, c t + c n)
          = (Y (n + 1) + c n) + ∑ t ∈ Finset.range n, c t := by ring
        _ ≤ (Y n + F * a n) + ∑ t ∈ Finset.range n, c t := add_le_add (hYstep n) le_rfl
        _ = (Y n + ∑ t ∈ Finset.range n, c t) + F * a n := by ring
        _ ≤ (r i + F * ∑ t ∈ Finset.range n, a t) + F * a n := add_le_add ih le_rfl
        _ = r i + (F * ∑ t ∈ Finset.range n, a t + F * a n) := by ring
  rw [hcost, hmean]
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  calc ∑ t ∈ Finset.range n, lpbG M C G t i
      ≤ ∑ t ∈ Finset.range (n + 1), lpbG M C G t i + V n := by
        refine le_trans (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ n))) ?_
        exact le_self_add
    _ = ∑ t ∈ Finset.range n, c t := hgpart n
    _ ≤ Y n + ∑ t ∈ Finset.range n, c t := le_add_self
    _ ≤ r i + F * ∑ t ∈ Finset.range n, a t := htel n
    _ ≤ r i + F * ∑' t, a t := by gcongr; exact ENNReal.sum_le_tsum (f := a) _

end SennottDP.MarkovCost.LPB

open SennottDP.MarkovCost SennottDP.MarkovCost.LPB in
theorem solution {S : Type} [Countable S] (M : MC S) (C : S → ℝ≥0) (z : S)
    (hm : ∀ i, meanPassage M {z} i < ⊤) (r : S → ℝ≥0) (Hs : Finset S) (hzH : z ∈ Hs)
    (hH : ∀ i ∈ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) < ⊤)
    (hdrift : ∀ i ∉ Hs, ∑' j, M.P i j * (r j : ℝ≥0∞) + C i ≤ r i) :
    (∃ F : ℝ≥0, ∀ i, i ≠ z → passageCost M C {z} i ≤ r i + F * meanPassage M {z} i) ∧
    (Hs = {z} → ∀ i, i ≠ z → passageCost M C {z} i ≤ r i) ∧
    passageCost M C {z} z < ⊤ := by
  set F : ℝ≥0 := ∑ k ∈ Hs, (∑' j, M.P k j * (r j : ℝ≥0∞) + C k).toNNReal with hF
  have hall : ∀ k, ∑' j, M.P k j * (r j : ℝ≥0∞) + C k ≤ r k + F := by
    intro k
    by_cases hkH : k ∈ Hs
    · have hfin : ∑' j, M.P k j * (r j : ℝ≥0∞) + C k ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨(hH k hkH).ne, ENNReal.coe_ne_top⟩
      rw [← ENNReal.coe_toNNReal hfin]
      refine le_trans ?_ le_add_self
      exact_mod_cast Finset.single_le_sum
        (f := fun k => (∑' j, M.P k j * (r j : ℝ≥0∞) + C k).toNNReal)
        (fun _ _ => bot_le) hkH
    · exact (hdrift k hkH).trans le_self_add
  have hgen : ∀ i, passageCost M C {z} i ≤ r i + F * meanPassage M {z} i := fun i =>
    lpb_cost_bound M C {z} i r F (fun t k _ => hall k) (hm i)
  refine ⟨⟨F, fun i _ => hgen i⟩, fun hHs i hi => ?_, ?_⟩
  · have hiG : i ∉ ({z} : Set S) := hi
    have h := lpb_cost_bound M C {z} i r 0 (fun t k hk => ?_) (hm i)
    · simpa using h
    · have hkG := lpb_reach M {z} i hiG t k hk
      have hkH : k ∉ Hs := by
        rw [hHs]; simpa using hkG
      simpa using hdrift k hkH
  · refine lt_of_le_of_lt (hgen z) ?_
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.coe_lt_top,
      ENNReal.mul_lt_top ENNReal.coe_lt_top (hm z)⟩


