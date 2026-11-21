-- Prove2me | solution 1 for OnlineTransportation1195.Main.strict_red_weight_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:16:13.743842+00:00
-- url     : https://prove2.me/submissions/92b3deda-55de-472d-b7d3-0ed3fe5ca5df

import Definitions.Def_OnlineTransportation1195_Main_RedPatches
import Mathlib

section
open scoped BigOperators
open Classical

namespace OnlineTransportation1195.Dev.L36
open OnlineTransportation1195.Main

variable {n : ℕ} (T : Tree n) (L : List (Fin n))

noncomputable def step (i : ℕ) : ℝ := T.downStep (T.vertexAt L i) (T.vertexAt L (i + 1))

noncomputable def Q (i : ℕ) : ℝ := ∑ j ∈ Finset.range i, step T L j

theorem step_nonneg (i : ℕ) : 0 ≤ step T L i := by
  unfold step Tree.downStep
  split_ifs with h
  · exact (T.W_pos _ h.1).le
  · exact le_refl _

theorem Q_succ (i : ℕ) : Q T L (i + 1) = Q T L i + step T L i := by
  unfold Q; rw [Finset.sum_range_succ]

theorem step_of_down {e : Fin n} {i : ℕ} (h : T.DownAt L e i) : step T L i = T.W e := by
  unfold step Tree.downStep
  obtain ⟨he, _, h1, h2⟩ := h
  rw [h2, h1]
  simp [he]

theorem step_eq_zero {i : ℕ} (h : ¬ ∃ e, T.DownAt L e i) : step T L i = 0 := by
  unfold step Tree.downStep
  split_ifs with hc
  · exfalso
    apply h
    refine ⟨T.vertexAt L (i + 1), hc.1, ?_, hc.2.symm, rfl⟩
    by_contra hlen
    apply hc.1
    unfold Tree.vertexAt
    rw [List.getD_eq_default]
    omega
  · rfl

theorem down_unique (hDFS : T.DFS L) {e : Fin n} (he : e ∈ T.edges) {i j : ℕ}
    (hi : T.DownAt L e i) (hj : T.DownAt L e j) : i = j := by
  have hc := (hDFS.2.2 e he).1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have hi' : (⟨i, by have := hi.2.1; omega⟩ : Fin L.length) ∈
      Finset.univ.filter (fun i : Fin L.length => T.DownAt L e i) := by simpa using hi
  have hj' : (⟨j, by have := hj.2.1; omega⟩ : Fin L.length) ∈
      Finset.univ.filter (fun i : Fin L.length => T.DownAt L e i) := by simpa using hj
  rw [ha, Finset.mem_singleton] at hi' hj'
  have := hi'.trans hj'.symm
  simpa using congrArg Fin.val this

theorem exists_down (hDFS : T.DFS L) {e : Fin n} (he : e ∈ T.edges) : ∃ i, T.DownAt L e i := by
  have hc := (hDFS.2.2 e he).1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
  have : a ∈ Finset.univ.filter (fun i : Fin L.length => T.DownAt L e i) := by rw [ha]; simp
  exact ⟨a.val, by simpa using this⟩

theorem x_eq (hDFS : T.DFS L) {e : Fin n} (he : e ∈ T.edges) {i : ℕ}
    (hi : T.DownAt L e i) : T.x L e = Q T L (i + 1) := by
  unfold Tree.x
  split
  · next i0 hfind =>
    have h0 : T.DownAt L e i0 := by
      have := List.find?_some hfind
      simpa using this
    rw [down_unique T L hDFS he h0 hi]
    rfl
  · next hfind =>
    exfalso
    have := List.find?_eq_none.mp hfind i (by simp; have := hi.2.1; omega)
    simp at this
    exact this hi


theorem Q_nonneg (i : ℕ) : 0 ≤ Q T L i :=
  Finset.sum_nonneg fun k _ => step_nonneg T L k

theorem W_le_x (hDFS : T.DFS L) {e : Fin n} (he : e ∈ T.edges) : T.W e ≤ T.x L e := by
  obtain ⟨i, hi⟩ := exists_down T L hDFS he
  rw [x_eq T L hDFS he hi, Q_succ, step_of_down T L hi]
  linarith [Q_nonneg T L i]

theorem sum_down (hDFS : T.DFS L) (g : ℕ → ℝ) {e : Fin n} (he : e ∈ T.edges) {i : ℕ}
    (hi : T.DownAt L e i) :
    ∑ j ∈ Finset.range L.length, (if T.DownAt L e j then g j else 0) = g i := by
  rw [Finset.sum_eq_single_of_mem i (by simp; have := hi.2.1; omega)]
  · simp [hi]
  · intro j _ hj
    rw [if_neg]
    intro hj'
    exact hj (down_unique T L hDFS he hj' hi)

theorem edge_mem_of_down {e : Fin n} {i : ℕ} (h : T.DownAt L e i) : e ∈ T.edges := by
  simp [Tree.edges, h.1]

theorem sum_range_eq_sum_edges (hDFS : T.DFS L) (H : ℕ → ℝ)
    (hH : ∀ j, (¬ ∃ e, T.DownAt L e j) → H j = 0) :
    ∑ j ∈ Finset.range L.length, H j =
      ∑ e ∈ T.edges, ∑ j ∈ Finset.range L.length, (if T.DownAt L e j then H j else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : ∃ e, T.DownAt L e j
  · obtain ⟨e, he⟩ := hj
    rw [Finset.sum_eq_single_of_mem e (edge_mem_of_down T L he)]
    · simp [he]
    · intro f _ hf
      rw [if_neg]
      intro hfj
      apply hf
      have h1 := hfj.2.2.2
      have h2 := he.2.2.2
      rw [← h1, ← h2]
  · rw [hH j hj]
    exact (Finset.sum_eq_zero fun e _ => by
      rw [if_neg]; exact fun h => hj ⟨e, h⟩).symm

theorem sum_W_eq_Q (hDFS : T.DFS L) : ∑ e ∈ T.edges, T.W e = Q T L L.length := by
  unfold Q
  rw [sum_range_eq_sum_edges T L hDFS (fun j => step T L j) (fun j hj => step_eq_zero T L hj)]
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨i, hi⟩ := exists_down T L hDFS he
  rw [sum_down T L hDFS _ he hi, step_of_down T L hi]

theorem tele (hDFS : T.DFS L) :
    ∑ e ∈ T.edges, (T.x L e ^ 2 - (T.x L e - T.W e) ^ 2) = (∑ e ∈ T.edges, T.W e) ^ 2 := by
  have h0 : ∀ j, (¬ ∃ e, T.DownAt L e j) →
      (fun j => Q T L (j + 1) ^ 2 - Q T L j ^ 2) j = 0 := by
    intro j hj
    simp only [Q_succ, step_eq_zero T L hj]; ring
  have h1 := sum_range_eq_sum_edges T L hDFS _ h0
  have h2 : ∑ j ∈ Finset.range L.length, (Q T L (j + 1) ^ 2 - Q T L j ^ 2) = Q T L L.length ^ 2 := by
    have := Finset.sum_range_sub (fun j => Q T L j ^ 2) L.length
    simpa [show Q T L 0 = 0 by simp [Q]] using this
  rw [sum_W_eq_Q T L hDFS, ← h2, h1]
  refine Finset.sum_congr rfl fun e he => ?_
  obtain ⟨i, hi⟩ := exists_down T L hDFS he
  rw [sum_down T L hDFS (fun j => Q T L (j + 1) ^ 2 - Q T L j ^ 2) he hi, x_eq T L hDFS he hi,
    Q_succ, step_of_down T L hi]
  ring

end OnlineTransportation1195.Dev.L36
end

section
open scoped BigOperators

namespace OnlineTransportation1195.Dev.L36b

/-- black length of an edge interval `(a, a+w]` at time `t`, deadline `d`. -/
noncomputable def bk (w a d t : ℝ) : ℝ := max 0 (min w (d - t - a))

theorem h_int {T : ℝ} (hT : 0 ≤ T) {c : ℝ} (hc : c ≤ T) :
    ∫ t in (0:ℝ)..T, max 0 (c - t) = (max c 0) ^ 2 / 2 := by
  rcases le_or_gt c 0 with h | h
  · have : ∫ t in (0:ℝ)..T, max 0 (c - t) = ∫ t in (0:ℝ)..T, (0:ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hT] at ht
      exact max_eq_left (by linarith [ht.1])
    rw [this, max_eq_right h]; simp
  · rw [← intervalIntegral.integral_add_adjacent_intervals (b := c)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    have h1 : ∫ t in (0:ℝ)..c, max 0 (c - t) = ∫ t in (0:ℝ)..c, (c - t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le h.le] at ht
      exact max_eq_right (by linarith [ht.2])
    have h2 : ∫ t in c..T, max 0 (c - t) = ∫ t in c..T, (0:ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hc] at ht
      exact max_eq_left (by linarith [ht.1])
    rw [h1, h2, intervalIntegral.integral_sub (by simp) (by apply Continuous.intervalIntegrable; fun_prop)]
    simp [max_eq_left h.le]
    ring

theorem bk_eq (w a d t : ℝ) (hw : 0 ≤ w) :
    bk w a d t = max 0 ((d - a) - t) - max 0 ((d - a - w) - t) := by
  unfold bk
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem bk_int {w a d T : ℝ} (hw : 0 ≤ w) (hT : 0 ≤ T) (hc : d - a ≤ T) :
    ∫ t in (0:ℝ)..T, bk w a d t =
      (max (d - a) 0) ^ 2 / 2 - (max (d - a - w) 0) ^ 2 / 2 := by
  have : ∀ t, bk w a d t = max 0 ((d - a) - t) - max 0 ((d - a - w) - t) := fun t => bk_eq w a d t hw
  simp_rw [this]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), h_int hT hc, h_int hT (by linarith)]

theorem bk_int_ge {w a d T : ℝ} (hw : 0 ≤ w) (hT : 0 ≤ T) (hc : d - a ≤ T) :
    w * (d - a) - w ^ 2 / 2 ≤ ∫ t in (0:ℝ)..T, bk w a d t := by
  rw [bk_int hw hT hc]
  rcases le_total 0 (d - a - w) with h | h
  · rw [max_eq_left h, max_eq_left (by linarith)]; nlinarith
  · rw [max_eq_right h]
    rcases le_total 0 (d - a) with h2 | h2
    · rw [max_eq_left h2]; nlinarith [sq_nonneg (d - a - w)]
    · rw [max_eq_right h2]; nlinarith

theorem c_int {w d T : ℝ} (hw : 0 ≤ w) (hd : 0 < d) (hT : 0 ≤ T) (hdT : d ≤ T) :
    ∫ t in (0:ℝ)..T, w * max 0 (1 - t / d) = w * d / 2 := by
  have : ∀ t : ℝ, w * max 0 (1 - t / d) = (w / d) * max 0 (d - t) := by
    intro t
    have : max 0 (1 - t / d) = (1 / d) * max 0 (d - t) := by
      rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 / d)]
      congr 1
      · simp
      · field_simp
    rw [this]; ring
  simp_rw [this]
  rw [intervalIntegral.integral_const_mul, h_int hT hdT, max_eq_left hd.le]
  field_simp

end OnlineTransportation1195.Dev.L36b
end

section
open scoped BigOperators

namespace OnlineTransportation1195.Dev.L36c
open OnlineTransportation1195.Dev.L36b

variable {ι : Type} [DecidableEq ι]

/-- F(t) -/
noncomputable def Fa (s : Finset ι) (w d : ι → ℝ) (t : ℝ) : ℝ := ∑ e ∈ s, w e * min 1 (t / d e)

/-- fractional red weight -/
noncomputable def Rt (s : Finset ι) (w a d : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ e ∈ s, (w e - bk (w e) (a e) (d e) t)

theorem sub_form (s : Finset ι) (w a d : ι → ℝ) (hd : ∀ e ∈ s, 0 < d e) (t : ℝ) :
    Fa s w d t - Rt s w a d t =
      ∑ e ∈ s, (bk (w e) (a e) (d e) t - w e * max 0 (1 - t / d e)) := by
  unfold Fa Rt
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e he => ?_
  rcases le_total 1 (t / d e) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_right (by linarith)]; ring

theorem exists_pos (s : Finset ι) (w a d : ι → ℝ) (hw : ∀ e ∈ s, 0 < w e)
    (hd : ∀ e ∈ s, 0 < d e) (ha : ∀ e ∈ s, 0 ≤ a e)
    (hsum : ∑ e ∈ s, w e / d e = 1)
    (htele : ∑ e ∈ s, w e * (2 * a e + w e) = (∑ e ∈ s, w e) ^ 2)
    (hne : ∃ e ∈ s, d e ≠ ∑ e ∈ s, w e) :
    ∃ t, 0 < t ∧ Rt s w a d t < Fa s w d t := by
  set W := ∑ e ∈ s, w e with hW
  set T : ℝ := ∑ e ∈ s, d e + 1 with hT
  have hdT : ∀ e ∈ s, d e ≤ T := by
    intro e he
    have := Finset.single_le_sum (f := d) (fun e he => (hd e he).le) he
    linarith
  have hT0 : 0 < T := by
    have : 0 ≤ ∑ e ∈ s, d e := Finset.sum_nonneg fun e he => (hd e he).le
    linarith
  by_contra hcon
  push Not at hcon
  -- G ≤ 0 on (0, T]
  have hG : ∫ t in (0:ℝ)..T, ∑ e ∈ s, (bk (w e) (a e) (d e) t - w e * max 0 (1 - t / d e)) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hT0.le]
    refine MeasureTheory.setIntegral_nonpos measurableSet_Ioc fun t ht => ?_
    rw [← sub_form s w a d hd]
    have := hcon t ht.1
    linarith
  have hint1 : ∀ e ∈ s, IntervalIntegrable (fun t => bk (w e) (a e) (d e) t) MeasureTheory.volume 0 T := by
    intro e _
    apply Continuous.intervalIntegrable
    unfold bk; fun_prop
  have hint2 : ∀ e ∈ s, IntervalIntegrable (fun t : ℝ => w e * max 0 (1 - t / d e)) MeasureTheory.volume 0 T := by
    intro e _
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun e he => (hint1 e he).sub (hint2 e he))] at hG
  have hlow : ∑ e ∈ s, (w e * (d e - a e) - w e ^ 2 / 2 - w e * d e / 2) ≤
      ∑ e ∈ s, ∫ t in (0:ℝ)..T,
        (bk (w e) (a e) (d e) t - w e * max 0 (1 - t / d e)) := by
    refine Finset.sum_le_sum fun e he => ?_
    rw [intervalIntegral.integral_sub (hint1 e he) (hint2 e he),
      c_int (hw e he).le (hd e he) hT0.le (hdT e he)]
    have := bk_int_ge (hw e he).le hT0.le (by linarith [hdT e he, ha e he] :
      d e - a e ≤ T) 
    linarith
  have hexpr : ∑ e ∈ s, (w e * (d e - a e) - w e ^ 2 / 2 - w e * d e / 2) =
      (∑ e ∈ s, w e * d e - W ^ 2) / 2 := by
    rw [← htele, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun e he => ?_
    ring
  have hpos : 0 < ∑ e ∈ s, w e * d e - W ^ 2 := by
    have h1 : ∑ e ∈ s, w e / d e * (d e - W) ^ 2 = ∑ e ∈ s, w e * d e - W ^ 2 := by
      have : ∀ e ∈ s, w e / d e * (d e - W) ^ 2 =
          w e * d e - 2 * W * w e + W ^ 2 * (w e / d e) := by
        intro e he
        have := (hd e he).ne'
        field_simp
        ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hsum, ← hW]
      ring
    rw [← h1]
    obtain ⟨e0, he0, hne0⟩ := hne
    refine Finset.sum_pos' (fun e he => ?_) ⟨e0, he0, ?_⟩
    · exact mul_nonneg (div_nonneg (hw e he).le (hd e he).le) (sq_nonneg _)
    · have := hw e0 he0; have := hd e0 he0
      have : 0 < (d e0 - W) ^ 2 := by
        have : d e0 - W ≠ 0 := sub_ne_zero.mpr hne0
        positivity
      positivity
  linarith

end OnlineTransportation1195.Dev.L36c
end

section
open scoped BigOperators

namespace OnlineTransportation1195.Dev.L36d
open OnlineTransportation1195.Dev.L36b OnlineTransportation1195.Dev.L36c

variable {ι : Type} [DecidableEq ι]

theorem bk_le (w a d t : ℝ) (hw : 0 ≤ w) : bk w a d t ≤ w := by
  unfold bk; exact max_le hw (min_le_left _ _)

theorem bk_nonneg (w a d t : ℝ) : 0 ≤ bk w a d t := le_max_left _ _

theorem bk_anti (w a d : ℝ) {t t' : ℝ} (h : t ≤ t') : bk w a d t' ≤ bk w a d t := by
  unfold bk
  exact max_le_max (le_refl _) (min_le_min (le_refl _) (by linarith))

theorem bk_partial {w a d t : ℝ} (h0 : 0 < bk w a d t) (h1 : bk w a d t < w) :
    bk w a d t = d - t - a := by
  unfold bk at *
  have : 0 < min w (d - t - a) := by
    by_contra hc
    rw [max_eq_left (not_lt.mp hc)] at h0
    exact lt_irrefl _ h0
  rw [max_eq_right this.le] at h1 ⊢
  have : d - t - a < w := by
    by_contra hc
    rw [min_eq_left (not_lt.mp hc)] at h1
    exact lt_irrefl _ h1
  rw [min_eq_right this.le]

/-- Fa is at most t. -/
theorem Fa_le (s : Finset ι) (w d : ι → ℝ) (hw : ∀ e ∈ s, 0 < w e) (hd : ∀ e ∈ s, 0 < d e)
    (hsum : ∑ e ∈ s, w e / d e = 1) {t : ℝ} (ht : 0 ≤ t) : Fa s w d t ≤ t := by
  calc Fa s w d t ≤ ∑ e ∈ s, t * (w e / d e) := by
        refine Finset.sum_le_sum fun e he => ?_
        have h := min_le_right 1 (t / d e)
        have := hw e he
        calc w e * min 1 (t / d e) ≤ w e * (t / d e) := by gcongr
          _ = t * (w e / d e) := by ring
    _ = t := by rw [← Finset.mul_sum, hsum, mul_one]

theorem Fa_lip (s : Finset ι) (w d : ι → ℝ) (hw : ∀ e ∈ s, 0 < w e) (hd : ∀ e ∈ s, 0 < d e)
    (hsum : ∑ e ∈ s, w e / d e = 1) {t t' : ℝ} (h : t' ≤ t) :
    Fa s w d t - Fa s w d t' ≤ t - t' := by
  unfold Fa
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ e ∈ s, (t - t') * (w e / d e) := by
        refine Finset.sum_le_sum fun e he => ?_
        have hdd := hd e he
        have hww := hw e he
        have : min 1 (t / d e) - min 1 (t' / d e) ≤ (t - t') / d e := by
          have h2 : (t - t') / d e = t / d e - t' / d e := by ring
          rw [h2]
          rcases le_total 1 (t' / d e) with h3 | h3
          · rw [min_eq_left h3, min_eq_left (h3.trans (by gcongr))]; linarith [(by gcongr : t' / d e ≤ t / d e)]
          · rw [min_eq_right h3]; linarith [min_le_right 1 (t / d e)]
        calc w e * min 1 (t / d e) - w e * min 1 (t' / d e)
            = w e * (min 1 (t / d e) - min 1 (t' / d e)) := by ring
          _ ≤ w e * ((t - t') / d e) := by gcongr
          _ = (t - t') * (w e / d e) := by ring
    _ = t - t' := by rw [← Finset.mul_sum, hsum, mul_one]

noncomputable def Rw (s : Finset ι) (w a d : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ e ∈ s.filter (fun e => bk (w e) (a e) (d e) t < w e), w e

theorem Rw_eq (s : Finset ι) (w a d : ι → ℝ) (hw : ∀ e ∈ s, 0 < w e) (t : ℝ)
    (hnp : ∀ e ∈ s, bk (w e) (a e) (d e) t = 0 ∨ bk (w e) (a e) (d e) t = w e) :
    Rw s w a d t = Rt s w a d t := by
  unfold Rw Rt
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun e he => ?_
  rcases hnp e he with h | h
  · rw [h, if_pos (hw e he)]; ring
  · rw [h, if_neg (lt_irrefl _)]; ring

theorem shift (s : Finset ι) (w a d : ι → ℝ) (hw : ∀ e ∈ s, 0 < w e)
    (hd : ∀ e ∈ s, 0 < d e) (hsum : ∑ e ∈ s, w e / d e = 1) :
    ∀ N : ℕ, ∀ t, 0 < t → Rt s w a d t < Fa s w d t →
      (s.filter (fun e => bk (w e) (a e) (d e) t < w e)).card ≤ N →
      ∃ t', 0 < t' ∧ Rw s w a d t' < Fa s w d t' := by
  intro N
  induction N with
  | zero =>
    intro t ht hR hN
    refine ⟨t, ht, ?_⟩
    have hnp : ∀ e ∈ s, bk (w e) (a e) (d e) t = 0 ∨ bk (w e) (a e) (d e) t = w e := by
      intro e he
      right
      have hle := bk_le (w e) (a e) (d e) t (hw e he).le
      by_contra hne
      have hlt : bk (w e) (a e) (d e) t < w e := lt_of_le_of_ne hle hne
      have : e ∈ s.filter (fun e => bk (w e) (a e) (d e) t < w e) := by simp [he, hlt]
      have := Finset.card_pos.mpr ⟨e, this⟩
      omega
    rw [Rw_eq s w a d hw t hnp]; exact hR
  | succ N ih =>
    intro t ht hR hN
    by_cases hnp : ∀ e ∈ s, bk (w e) (a e) (d e) t = 0 ∨ bk (w e) (a e) (d e) t = w e
    · exact ⟨t, ht, by rw [Rw_eq s w a d hw t hnp]; exact hR⟩
    · push Not at hnp
      obtain ⟨e, he, h0, h1⟩ := hnp
      have hb0 : 0 < bk (w e) (a e) (d e) t := lt_of_le_of_ne (bk_nonneg _ _ _ _) (Ne.symm h0)
      have hb1 : bk (w e) (a e) (d e) t < w e :=
        lt_of_le_of_ne (bk_le _ _ _ _ (hw e he).le) h1
      set q := w e - bk (w e) (a e) (d e) t with hq
      have hqpos : 0 < q := by rw [hq]; linarith
      have hRle : q ≤ Rt s w a d t := by
        unfold Rt
        have := Finset.single_le_sum (f := fun e => w e - bk (w e) (a e) (d e) t)
          (fun e he => sub_nonneg.mpr (bk_le _ _ _ _ (hw e he).le)) he
        exact this
      have hFt := Fa_le s w d hw hd hsum ht.le
      have htq : q < t := by linarith
      refine ih (t - q) (by linarith) ?_ ?_
      · -- G(t*) ≥ G(t) > 0
        have hF := Fa_lip s w d hw hd hsum (t := t) (t' := t - q) (by linarith)
        have hRs : Rt s w a d (t - q) ≤ Rt s w a d t - q := by
          unfold Rt
          have hbe : bk (w e) (a e) (d e) (t - q) = w e := by
            have := bk_partial hb0 hb1
            unfold bk
            rw [show d e - (t - q) - a e = w e by rw [hq]; linarith]
            simp [(hw e he).le]
          rw [← Finset.add_sum_erase s _ he, ← Finset.add_sum_erase s _ he, hbe]
          have : ∑ x ∈ s.erase e, (w x - bk (w x) (a x) (d x) (t - q)) ≤
              ∑ x ∈ s.erase e, (w x - bk (w x) (a x) (d x) t) :=
            Finset.sum_le_sum fun x hx => by
              have := bk_anti (w x) (a x) (d x) (t := t - q) (t' := t) (by linarith)
              linarith
          linarith
        linarith
      · -- fewer red edges
        have hsub : s.filter (fun x => bk (w x) (a x) (d x) (t - q) < w x) ⊆
            (s.filter (fun x => bk (w x) (a x) (d x) t < w x)).erase e := by
          intro x hx
          rw [Finset.mem_filter] at hx
          rw [Finset.mem_erase, Finset.mem_filter]
          refine ⟨?_, hx.1, ?_⟩
          · rintro rfl
            have hbe : bk (w x) (a x) (d x) (t - q) = w x := by
              have := bk_partial hb0 hb1
              unfold bk
              rw [show d x - (t - q) - a x = w x by rw [hq]; linarith]
              simp [(hw x he).le]
            rw [hbe] at hx; exact lt_irrefl _ hx.2
          · exact lt_of_le_of_lt (bk_anti (w x) (a x) (d x) (t := t - q) (t' := t) (by linarith)) hx.2 |>.trans_le' (le_refl _) |> fun h => by
              have := bk_anti (w x) (a x) (d x) (t := t - q) (t' := t) (by linarith)
              exact lt_of_le_of_lt this hx.2
        have hmem : e ∈ s.filter (fun x => bk (w x) (a x) (d x) t < w x) := by simp [he, hb1]
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hmem] at this
        omega

end OnlineTransportation1195.Dev.L36d
end

section
open scoped BigOperators
open Classical

namespace OnlineTransportation1195.Dev.L36e
open OnlineTransportation1195.Main OnlineTransportation1195.Dev.L36 OnlineTransportation1195.Dev.L36b
  OnlineTransportation1195.Dev.L36c OnlineTransportation1195.Dev.L36d

theorem main {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
    (L : List (Fin n)) (hD : T.Normalized d) (hDFS : T.DFS L)
    (hne : T.Unequal d) :
    ∃ t : ℝ, 0 < t ∧ T.R d L t < T.F d t := by
  have hwpos : ∀ e ∈ T.edges, 0 < T.W e := fun e he => by
    have : e ≠ T.root := by simpa [Tree.edges] using he
    exact T.W_pos e this
  have hdpos := hD.1
  have hsum := hD.2.2
  have hW := tele T L hDFS
  obtain ⟨t, ht, hlt⟩ := exists_pos T.edges T.W (fun e => T.x L e - T.W e) d hwpos hdpos
    (fun e he => sub_nonneg.mpr (W_le_x T L hDFS he)) hsum
    (by
      rw [← hW]
      refine Finset.sum_congr rfl fun e _ => ?_
      ring)
    (by
      obtain ⟨e, he, f, hf, hef⟩ := hne
      by_cases h : d e = ∑ e ∈ T.edges, T.W e
      · exact ⟨f, hf, fun h' => hef (h.trans h'.symm)⟩
      · exact ⟨e, he, h⟩)
  obtain ⟨t', ht', hlt'⟩ := shift T.edges T.W (fun e => T.x L e - T.W e) d hwpos hdpos hsum _ t ht hlt le_rfl
  refine ⟨t', ht', ?_⟩
  have hfil : T.edges.filter (fun e => bk (T.W e) (T.x L e - T.W e) (d e) t' < T.W e) = T.red d L t' := by
    unfold Tree.red
    refine Finset.filter_congr fun e he => ?_
    have hw := hwpos e he
    unfold bk
    rw [max_lt_iff, min_lt_iff]
    constructor
    · rintro ⟨_, h | h⟩
      · linarith
      · linarith
    · intro h
      exact ⟨hw, Or.inr (by linarith)⟩
  unfold Rw at hlt'
  rw [hfil] at hlt'
  exact hlt'

end OnlineTransportation1195.Dev.L36e

namespace OnlineTransportation1195.Main
open OnlineTransportation1195.Dev.L36e in
theorem chk_strict_red_weight_budget {n : ℕ} (T : Tree n) (d : Fin n → ℝ)
    (L : List (Fin n)) (hD : T.Normalized d) (hDFS : T.DFS L)
    (hne : T.Unequal d) :
    ∃ t : ℝ, 0 < t ∧ T.R d L t < T.F d t := main T d L hD hDFS hne
end OnlineTransportation1195.Main
end

theorem solution : type_of% @OnlineTransportation1195.Main.chk_strict_red_weight_budget := @OnlineTransportation1195.Main.chk_strict_red_weight_budget
