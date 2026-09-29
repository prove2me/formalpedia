-- Prove2me | solution 1 for PLCMarkets.Rationality.lp_optimal_value_eq_total_money
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:33:10.599986+00:00
-- url     : https://prove2.me/submissions/1949efeb-1f71-46eb-98a9-0c826f060cf9

import Mathlib
import Definitions.Def_PLCMarkets_Rationality_RationalityLP

namespace PLCMarkets.Rationality

/-- Total amount of the segments with slope strictly above `c`. -/
noncomputable def aux_lpo_Agt (L : List (ℚ × ℚ)) (c : ℝ) : ℝ :=
  (L.map (fun s => if c < (s.1 : ℝ) then (s.2 : ℝ) else 0)).sum

/-- Total amount of the segments with slope at least `c`. -/
noncomputable def aux_lpo_Age (L : List (ℚ × ℚ)) (c : ℝ) : ℝ :=
  (L.map (fun s => if c ≤ (s.1 : ℝ) then (s.2 : ℝ) else 0)).sum

lemma aux_lpo_Agt_cons (s : ℚ × ℚ) (L : List (ℚ × ℚ)) (c : ℝ) :
    aux_lpo_Agt (s :: L) c = (if c < (s.1 : ℝ) then (s.2 : ℝ) else 0) + aux_lpo_Agt L c := by
  simp [aux_lpo_Agt]

lemma aux_lpo_Age_cons (s : ℚ × ℚ) (L : List (ℚ × ℚ)) (c : ℝ) :
    aux_lpo_Age (s :: L) c = (if c ≤ (s.1 : ℝ) then (s.2 : ℝ) else 0) + aux_lpo_Age L c := by
  simp [aux_lpo_Age]

lemma aux_lpo_Agt_append (L1 L2 : List (ℚ × ℚ)) (c : ℝ) :
    aux_lpo_Agt (L1 ++ L2) c = aux_lpo_Agt L1 c + aux_lpo_Agt L2 c := by
  simp [aux_lpo_Agt]

lemma aux_lpo_Age_append (L1 L2 : List (ℚ × ℚ)) (c : ℝ) :
    aux_lpo_Age (L1 ++ L2) c = aux_lpo_Age L1 c + aux_lpo_Age L2 c := by
  simp [aux_lpo_Age]

lemma aux_lpo_Agt_nonneg (L : List (ℚ × ℚ)) (hL : ∀ s ∈ L, 0 ≤ s.2) (c : ℝ) :
    0 ≤ aux_lpo_Agt L c := by
  unfold aux_lpo_Agt
  apply List.sum_nonneg
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  split_ifs
  · exact_mod_cast hL s hs
  · exact le_rfl

lemma aux_lpo_Age_nonneg (L : List (ℚ × ℚ)) (hL : ∀ s ∈ L, 0 ≤ s.2) (c : ℝ) :
    0 ≤ aux_lpo_Age L c := by
  unfold aux_lpo_Age
  apply List.sum_nonneg
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  split_ifs
  · exact_mod_cast hL s hs
  · exact le_rfl

lemma aux_lpo_Agt_eq_zero (L : List (ℚ × ℚ)) (c : ℝ) (h : ∀ s ∈ L, (s.1 : ℝ) ≤ c) :
    aux_lpo_Agt L c = 0 := by
  unfold aux_lpo_Agt
  apply List.sum_eq_zero
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  rw [if_neg (not_lt.mpr (h s hs))]

lemma aux_lpo_Age_eq_zero (L : List (ℚ × ℚ)) (c : ℝ) (h : ∀ s ∈ L, (s.1 : ℝ) < c) :
    aux_lpo_Age L c = 0 := by
  unfold aux_lpo_Age
  apply List.sum_eq_zero
  intro y hy
  simp only [List.mem_map] at hy
  obtain ⟨s, hs, rfl⟩ := hy
  rw [if_neg (not_le.mpr (h s hs))]

lemma aux_lpo_plEval_nonpos (L : List (ℚ × ℚ)) (hL : ∀ s ∈ L, 0 ≤ s.2) (x : ℝ) (hx : x ≤ 0) :
    plEval L x = 0 := by
  induction L generalizing x with
  | nil => simp [plEval]
  | cons s rest ih =>
    obtain ⟨c, a⟩ := s
    have ha : (0:ℝ) ≤ a := by exact_mod_cast hL (c, a) (by simp)
    simp only [plEval]
    rw [ih (fun t ht => hL t (by simp [ht])) (x - a) (by linarith)]
    rw [max_eq_right hx, min_eq_left ha]; ring

lemma aux_lpo_plEval_append (L1 L2 : List (ℚ × ℚ)) (x : ℝ) :
    plEval (L1 ++ L2) x = plEval L1 x + plEval L2 (x - (((L1.map Prod.snd).sum : ℚ) : ℝ)) := by
  induction L1 generalizing x with
  | nil => simp [plEval]
  | cons s rest ih =>
    obtain ⟨c, a⟩ := s
    simp only [List.cons_append, plEval, ih, List.map_cons, List.sum_cons]
    push_cast
    rw [sub_sub]; ring

lemma aux_lpo_clamp_mono (a u v : ℝ) (huv : u ≤ v) : min (max u 0) a ≤ min (max v 0) a := by
  simp only [max_def, min_def]; split_ifs <;> linarith

lemma aux_lpo_clamp_lip (a u v : ℝ) (huv : u ≤ v) :
    min (max v 0) a - min (max u 0) a ≤ v - u := by
  simp only [max_def, min_def]; split_ifs <;> linarith

lemma aux_lpo_clamp_ge (a u : ℝ) (hu : u ≤ a) : u ≤ min (max u 0) a := by
  simp only [max_def, min_def]; split_ifs <;> linarith

lemma aux_lpo_clamp_top (a u : ℝ) (ha : 0 ≤ a) (hu : a ≤ u) : min (max u 0) a = a := by
  simp only [max_def, min_def]; split_ifs <;> linarith

lemma aux_lpo_clamp_mid (a u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ a) : min (max u 0) a = u := by
  simp only [max_def, min_def]; split_ifs <;> linarith

/-- Upper bound when every slope is at most `c`. -/
lemma aux_lpo_ub (L : List (ℚ × ℚ)) (hA : ∀ s ∈ L, 0 ≤ s.2) (hS : ∀ s ∈ L, 0 ≤ s.1)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ s ∈ L, (s.1 : ℝ) ≤ c) (u v : ℝ) (huv : u ≤ v) :
    plEval L v - plEval L u ≤ c * (v - u) := by
  induction L generalizing u v with
  | nil => simp only [plEval, sub_self]; exact mul_nonneg hc0 (by linarith)
  | cons s rest ih =>
    obtain ⟨sl, a⟩ := s
    have ha : (0:ℝ) ≤ a := by exact_mod_cast hA (sl, a) (by simp)
    have hsl0 : (0:ℝ) ≤ sl := by exact_mod_cast hS (sl, a) (by simp)
    have hslc : (sl:ℝ) ≤ c := hc (sl, a) (by simp)
    have hA' : ∀ t ∈ rest, 0 ≤ t.2 := fun t ht => hA t (by simp [ht])
    have hS' : ∀ t ∈ rest, 0 ≤ t.1 := fun t ht => hS t (by simp [ht])
    have hc' : ∀ t ∈ rest, (t.1:ℝ) ≤ c := fun t ht => hc t (by simp [ht])
    have ih' := ih hA' hS' hc'
    have h0 := aux_lpo_plEval_nonpos rest hA'
    simp only [plEval]
    rcases le_or_gt v a with hva | hav
    · rw [h0 (v - a) (by linarith), h0 (u - a) (by linarith)]
      have h1 := aux_lpo_clamp_mono a u v huv
      have h2 := aux_lpo_clamp_lip a u v huv
      nlinarith [mul_nonneg hsl0 (sub_nonneg.mpr h2),
        mul_nonneg (sub_nonneg.mpr hslc) (sub_nonneg.mpr huv)]
    · rcases le_or_gt (a:ℝ) u with hau | hua
      · rw [aux_lpo_clamp_top a v ha hav.le, aux_lpo_clamp_top a u ha hau]
        have := ih' (u - a) (v - a) (by linarith)
        rw [show v - (a:ℝ) - (u - a) = v - u by ring] at this
        linarith
      · rw [aux_lpo_clamp_top a v ha hav.le, h0 (u - a) (by linarith)]
        have h3 := ih' 0 (v - a) (by linarith)
        rw [h0 0 le_rfl] at h3
        have h4 := aux_lpo_clamp_ge a u hua.le
        have h5 : min (max u 0) (a:ℝ) ≤ a := min_le_right _ _
        nlinarith [mul_nonneg hsl0 (sub_nonneg.mpr h4),
          mul_nonneg (sub_nonneg.mpr hslc) (sub_nonneg.mpr h5)]

lemma aux_lpo_ub_strict (L : List (ℚ × ℚ)) (hA : ∀ s ∈ L, 0 ≤ s.2) (hS : ∀ s ∈ L, 0 ≤ s.1)
    (c : ℝ) (hc0 : 0 < c) (hc : ∀ s ∈ L, (s.1 : ℝ) < c) (u v : ℝ) (huv : u < v) :
    plEval L v - plEval L u < c * (v - u) := by
  have : ∃ c' : ℝ, c' < c ∧ 0 ≤ c' ∧ ∀ s ∈ L, (s.1 : ℝ) ≤ c' := by
    clear hA hS
    induction L with
    | nil => exact ⟨0, hc0, le_rfl, by simp⟩
    | cons s rest ih =>
      obtain ⟨c', h1, h2, h3⟩ := ih (fun t ht => hc t (by simp [ht]))
      refine ⟨max (s.1 : ℝ) c', max_lt (hc s (by simp)) h1, le_trans h2 (le_max_right _ _), ?_⟩
      intro t ht
      rcases List.mem_cons.mp ht with h | h
      · rw [h]; exact le_max_left _ _
      · exact le_trans (h3 t h) (le_max_right _ _)
  obtain ⟨c', h1, h2, h3⟩ := this
  have := aux_lpo_ub L hA hS c' h2 h3 u v huv.le
  have : c' * (v - u) < c * (v - u) := mul_lt_mul_of_pos_right h1 (by linarith)
  linarith

/-- Strict lower bound below the total amount of the segments with slope `> c`. -/
lemma aux_lpo_lb_strict (L : List (ℚ × ℚ)) (hA : ∀ s ∈ L, 0 ≤ s.2)
    (hanti : L.Pairwise (fun s t => t.1 ≤ s.1)) (c : ℝ) (u v : ℝ) (hu : 0 ≤ u) (huv : u < v)
    (hv : v ≤ aux_lpo_Agt L c) : c * (v - u) < plEval L v - plEval L u := by
  induction L generalizing u v with
  | nil => simp [aux_lpo_Agt] at hv; linarith
  | cons s rest ih =>
    obtain ⟨sl, a⟩ := s
    rw [List.pairwise_cons] at hanti
    obtain ⟨hhead, hrest⟩ := hanti
    have ha : (0:ℝ) ≤ a := by exact_mod_cast hA (sl, a) (by simp)
    have hA' : ∀ t ∈ rest, 0 ≤ t.2 := fun t ht => hA t (by simp [ht])
    have h0 := aux_lpo_plEval_nonpos rest hA'
    rw [aux_lpo_Agt_cons] at hv
    by_cases hs : c < (sl:ℝ)
    · rw [if_pos hs] at hv
      simp only [plEval]
      rcases le_or_gt v a with hva | hav
      · rw [h0 (v - a) (by linarith), h0 (u - a) (by linarith),
          aux_lpo_clamp_mid a v (by linarith) hva, aux_lpo_clamp_mid a u hu (by linarith)]
        nlinarith
      · rcases le_or_gt (a:ℝ) u with hau | hua
        · rw [aux_lpo_clamp_top a v ha hav.le, aux_lpo_clamp_top a u ha hau]
          have := ih hA' hrest (u - a) (v - a) (by linarith) (by linarith) (by linarith)
          rw [show v - (a:ℝ) - (u - a) = v - u by ring] at this
          linarith
        · rw [aux_lpo_clamp_top a v ha hav.le, aux_lpo_clamp_mid a u hu hua.le,
            h0 (u - a) (by linarith)]
          have h3 := ih hA' hrest 0 (v - a) le_rfl (by linarith) (by linarith)
          rw [h0 0 le_rfl] at h3
          have h4 : c * (a - u) < sl * (a - u) := mul_lt_mul_of_pos_right hs (by linarith)
          nlinarith
    · rw [if_neg hs] at hv
      have : aux_lpo_Agt rest c = 0 := aux_lpo_Agt_eq_zero rest c
        (fun t ht => le_trans (by exact_mod_cast hhead t ht) (not_lt.mp hs))
      linarith

/-- Lower bound below the total amount of the segments with slope `≥ c`. -/
lemma aux_lpo_lb (L : List (ℚ × ℚ)) (hA : ∀ s ∈ L, 0 ≤ s.2)
    (hanti : L.Pairwise (fun s t => t.1 ≤ s.1)) (c : ℝ) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v ≤ aux_lpo_Age L c) : c * (v - u) ≤ plEval L v - plEval L u := by
  induction L generalizing u v with
  | nil =>
    simp [aux_lpo_Age] at hv
    have : u = v := by linarith
    subst this; simp
  | cons s rest ih =>
    obtain ⟨sl, a⟩ := s
    rw [List.pairwise_cons] at hanti
    obtain ⟨hhead, hrest⟩ := hanti
    have ha : (0:ℝ) ≤ a := by exact_mod_cast hA (sl, a) (by simp)
    have hA' : ∀ t ∈ rest, 0 ≤ t.2 := fun t ht => hA t (by simp [ht])
    have h0 := aux_lpo_plEval_nonpos rest hA'
    rw [aux_lpo_Age_cons] at hv
    by_cases hs : c ≤ (sl:ℝ)
    · rw [if_pos hs] at hv
      simp only [plEval]
      rcases le_or_gt v a with hva | hav
      · rw [h0 (v - a) (by linarith), h0 (u - a) (by linarith),
          aux_lpo_clamp_mid a v (by linarith) hva, aux_lpo_clamp_mid a u hu (by linarith)]
        nlinarith
      · rcases le_or_gt (a:ℝ) u with hau | hua
        · rw [aux_lpo_clamp_top a v ha hav.le, aux_lpo_clamp_top a u ha hau]
          have := ih hA' hrest (u - a) (v - a) (by linarith) (by linarith) (by linarith)
          rw [show v - (a:ℝ) - (u - a) = v - u by ring] at this
          linarith
        · rw [aux_lpo_clamp_top a v ha hav.le, aux_lpo_clamp_mid a u hu hua.le,
            h0 (u - a) (by linarith)]
          have h3 := ih hA' hrest 0 (v - a) le_rfl (by linarith) (by linarith)
          rw [h0 0 le_rfl] at h3
          have h4 : c * (a - u) ≤ sl * (a - u) := mul_le_mul_of_nonneg_right hs (by linarith)
          nlinarith
    · rw [if_neg hs] at hv
      have : aux_lpo_Age rest c = 0 := aux_lpo_Age_eq_zero rest c
        (fun t ht => lt_of_le_of_lt (by exact_mod_cast hhead t ht) (not_le.mp hs))
      have : u = v := by linarith
      subst this; simp

/-- Upper bound beyond the total amount of the segments with slope `> c`. -/
lemma aux_lpo_ub_gt (L : List (ℚ × ℚ)) (hA : ∀ s ∈ L, 0 ≤ s.2) (hS : ∀ s ∈ L, 0 ≤ s.1)
    (hanti : L.Pairwise (fun s t => t.1 ≤ s.1)) (c : ℝ) (hc0 : 0 ≤ c) (u v : ℝ)
    (hu : aux_lpo_Agt L c ≤ u) (huv : u ≤ v) : plEval L v - plEval L u ≤ c * (v - u) := by
  induction L generalizing u v with
  | nil => simp only [plEval, sub_self]; exact mul_nonneg hc0 (by linarith)
  | cons s rest ih =>
    obtain ⟨sl, a⟩ := s
    rw [List.pairwise_cons] at hanti
    obtain ⟨hhead, hrest⟩ := hanti
    have ha : (0:ℝ) ≤ a := by exact_mod_cast hA (sl, a) (by simp)
    have hA' : ∀ t ∈ rest, 0 ≤ t.2 := fun t ht => hA t (by simp [ht])
    have hS' : ∀ t ∈ rest, 0 ≤ t.1 := fun t ht => hS t (by simp [ht])
    rw [aux_lpo_Agt_cons] at hu
    by_cases hs : c < (sl:ℝ)
    · rw [if_pos hs] at hu
      have hnn := aux_lpo_Agt_nonneg rest hA' c
      simp only [plEval]
      rw [aux_lpo_clamp_top a v ha (by linarith), aux_lpo_clamp_top a u ha (by linarith)]
      have := ih hA' hS' hrest (u - a) (v - a) (by linarith) (by linarith)
      rw [show v - (a:ℝ) - (u - a) = v - u by ring] at this
      linarith
    · apply aux_lpo_ub ((sl, a) :: rest) hA hS c hc0 _ u v huv
      intro t ht
      rcases List.mem_cons.mp ht with h | h
      · rw [h]; exact not_lt.mp hs
      · exact le_trans (by exact_mod_cast hhead t h) (not_lt.mp hs)

/-- Strict upper bound beyond the total amount of the segments with slope `≥ c`. -/
lemma aux_lpo_ub_ge (L : List (ℚ × ℚ)) (hA : ∀ s ∈ L, 0 ≤ s.2) (hS : ∀ s ∈ L, 0 ≤ s.1)
    (hanti : L.Pairwise (fun s t => t.1 ≤ s.1)) (c : ℝ) (hc0 : 0 < c) (u v : ℝ)
    (hu : aux_lpo_Age L c ≤ u) (huv : u < v) : plEval L v - plEval L u < c * (v - u) := by
  induction L generalizing u v with
  | nil => simp only [plEval, sub_self]; exact mul_pos hc0 (by linarith)
  | cons s rest ih =>
    obtain ⟨sl, a⟩ := s
    rw [List.pairwise_cons] at hanti
    obtain ⟨hhead, hrest⟩ := hanti
    have ha : (0:ℝ) ≤ a := by exact_mod_cast hA (sl, a) (by simp)
    have hA' : ∀ t ∈ rest, 0 ≤ t.2 := fun t ht => hA t (by simp [ht])
    have hS' : ∀ t ∈ rest, 0 ≤ t.1 := fun t ht => hS t (by simp [ht])
    rw [aux_lpo_Age_cons] at hu
    by_cases hs : c ≤ (sl:ℝ)
    · rw [if_pos hs] at hu
      have hnn := aux_lpo_Age_nonneg rest hA' c
      simp only [plEval]
      rw [aux_lpo_clamp_top a v ha (by linarith), aux_lpo_clamp_top a u ha (by linarith)]
      have := ih hA' hS' hrest (u - a) (v - a) (by linarith) (by linarith)
      rw [show v - (a:ℝ) - (u - a) = v - u by ring] at this
      linarith
    · apply aux_lpo_ub_strict ((sl, a) :: rest) hA hS c hc0 _ u v huv
      intro t ht
      rcases List.mem_cons.mp ht with h | h
      · rw [h]; exact not_le.mp hs
      · exact lt_of_le_of_lt (by exact_mod_cast hhead t h) (not_le.mp hs)

/-! Evaluation-level bounds. -/

lemma aux_lpo_segs_amt (f : PLConcave) : ∀ s ∈ f.segs, (0:ℚ) ≤ s.2 :=
  fun s hs => le_of_lt (f.amount_pos s hs)

lemma aux_lpo_eval_eq (f : PLConcave) (B : ℚ) (hB : 0 < B) (x : ℝ) (hx : x ≤ B) :
    f.eval x = plEval (f.segs ++ [(f.tail, B)]) x := by
  have hT : (0:ℝ) ≤ (((f.segs.map Prod.snd).sum : ℚ) : ℝ) := by
    have : (0:ℚ) ≤ (f.segs.map Prod.snd).sum := by
      apply List.sum_nonneg
      intro y hy
      simp only [List.mem_map] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      exact aux_lpo_segs_amt f s hs
    exact_mod_cast this
  have hB' : (0:ℝ) < B := by exact_mod_cast hB
  rw [aux_lpo_plEval_append]
  simp only [PLConcave.eval, plEval]
  rw [min_eq_left (max_le (by linarith) hB'.le)]
  ring

lemma aux_lpo_ext_props (f : PLConcave) (B : ℚ) (hB : 0 < B) :
    (∀ s ∈ f.segs ++ [(f.tail, B)], (0:ℚ) ≤ s.2) ∧
    (∀ s ∈ f.segs ++ [(f.tail, B)], (0:ℚ) ≤ s.1) ∧
    (f.segs ++ [(f.tail, B)]).Pairwise (fun s t => t.1 ≤ s.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    rcases List.mem_append.mp hs with h | h
    · exact aux_lpo_segs_amt f s h
    · simp at h; rw [h]; exact hB.le
  · intro s hs
    rcases List.mem_append.mp hs with h | h
    · exact f.slope_nonneg s h
    · simp at h; rw [h]; exact f.tail_nonneg
  · rw [List.pairwise_append]
    refine ⟨f.slope_antitone, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp at hb; rw [hb]; exact f.tail_le a ha

lemma aux_lpo_bigB (v : ℝ) : ∃ B : ℚ, 0 < B ∧ v ≤ (B : ℝ) := by
  refine ⟨(Nat.ceil v : ℚ) + 1, by positivity, ?_⟩
  push_cast
  linarith [Nat.le_ceil v]

lemma aux_lpo_E1 (f : PLConcave) (c : ℝ) (hc : (f.tail : ℝ) ≤ c) (u v : ℝ) (hu : 0 ≤ u)
    (huv : u < v) (hv : v ≤ aux_lpo_Agt f.segs c) : c * (v - u) < f.eval v - f.eval u := by
  obtain ⟨B, hB, hvB⟩ := aux_lpo_bigB v
  obtain ⟨hA, _, hanti⟩ := aux_lpo_ext_props f B hB
  rw [aux_lpo_eval_eq f B hB v hvB, aux_lpo_eval_eq f B hB u (by linarith)]
  apply aux_lpo_lb_strict _ hA hanti c u v hu huv
  rw [aux_lpo_Agt_append, aux_lpo_Agt_cons, if_neg (not_lt.mpr hc)]
  have hnil : aux_lpo_Agt [] c = 0 := by simp [aux_lpo_Agt]
  rw [hnil]
  linarith

lemma aux_lpo_E2 (f : PLConcave) (c : ℝ) (hc0 : 0 ≤ c) (hc : (f.tail : ℝ) ≤ c) (u v : ℝ)
    (hu : aux_lpo_Agt f.segs c ≤ u) (huv : u ≤ v) : f.eval v - f.eval u ≤ c * (v - u) := by
  obtain ⟨B, hB, hvB⟩ := aux_lpo_bigB v
  obtain ⟨hA, hS, hanti⟩ := aux_lpo_ext_props f B hB
  rw [aux_lpo_eval_eq f B hB v hvB, aux_lpo_eval_eq f B hB u (by linarith)]
  apply aux_lpo_ub_gt _ hA hS hanti c hc0 u v _ huv
  rw [aux_lpo_Agt_append, aux_lpo_Agt_cons, if_neg (not_lt.mpr hc)]
  have hnil : aux_lpo_Agt [] c = 0 := by simp [aux_lpo_Agt]
  rw [hnil]
  linarith

lemma aux_lpo_E3 (f : PLConcave) (c : ℝ) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v ≤ aux_lpo_Age f.segs c ∨ (f.tail : ℝ) = c) : c * (v - u) ≤ f.eval v - f.eval u := by
  obtain ⟨B, hB, hvB⟩ := aux_lpo_bigB v
  obtain ⟨hA, _, hanti⟩ := aux_lpo_ext_props f B hB
  rw [aux_lpo_eval_eq f B hB v hvB, aux_lpo_eval_eq f B hB u (by linarith)]
  apply aux_lpo_lb _ hA hanti c u v hu huv
  rw [aux_lpo_Age_append, aux_lpo_Age_cons]
  have h0 := aux_lpo_Age_nonneg f.segs (aux_lpo_segs_amt f) c
  have hnil : aux_lpo_Age [] c = 0 := by simp [aux_lpo_Age]
  rw [hnil]
  have hB' : (0:ℝ) < B := by exact_mod_cast hB
  rcases hv with h | h
  · split_ifs <;> linarith
  · rw [if_pos (le_of_eq h.symm)]; linarith

lemma aux_lpo_E4 (f : PLConcave) (c : ℝ) (hc : (f.tail : ℝ) < c) (u v : ℝ)
    (hu : aux_lpo_Age f.segs c ≤ u) (huv : u < v) : f.eval v - f.eval u < c * (v - u) := by
  obtain ⟨B, hB, hvB⟩ := aux_lpo_bigB v
  obtain ⟨hA, hS, hanti⟩ := aux_lpo_ext_props f B hB
  have hc0 : 0 < c := lt_of_le_of_lt (by exact_mod_cast f.tail_nonneg) hc
  rw [aux_lpo_eval_eq f B hB v hvB, aux_lpo_eval_eq f B hB u (by linarith)]
  apply aux_lpo_ub_ge _ hA hS hanti c hc0 u v _ huv
  rw [aux_lpo_Age_append, aux_lpo_Age_cons, if_neg (not_le.mpr hc)]
  have hnil : aux_lpo_Age [] c = 0 := by simp [aux_lpo_Age]
  rw [hnil]
  linarith

/-! Conversions between the platform's sums and the list-level quantities. -/

lemma aux_lpo_forcedAmount_eq {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n)
    (j : Fin g) (hp : 0 < p j) :
    M.forcedAmount p i j = aux_lpo_Agt (M.util i j).segs (M.flexBpb p i * p j) := by
  classical
  unfold FisherMarket.forcedAmount aux_lpo_Agt
  rw [Finset.sum_filter, ← Fin.sum_univ_fun_getElem]
  apply Finset.sum_congr rfl
  intro k _
  have hiff : M.IsForcedSeg p (⟨j, k⟩ : M.Seg i) ↔
      M.flexBpb p i * p j < (((M.util i j).segs[k.1]).1 : ℝ) := by
    simp only [FisherMarket.IsForcedSeg, FisherMarket.segBpb, FisherMarket.segSlope,
      List.get_eq_getElem]
    exact lt_div_iff₀ hp
  by_cases h : M.flexBpb p i * p j < (((M.util i j).segs[k.1]).1 : ℝ)
  · rw [if_pos (hiff.mpr h), if_pos h]; rfl
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

lemma aux_lpo_flexCapLP_eq {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n)
    (j : Fin g) (hp : 0 < p j) :
    M.flexCapLP p j i p = p j * (aux_lpo_Age (M.util i j).segs (M.flexBpb p i * p j) -
      aux_lpo_Agt (M.util i j).segs (M.flexBpb p i * p j)) := by
  classical
  unfold FisherMarket.flexCapLP aux_lpo_Agt aux_lpo_Age
  rw [Finset.sum_filter, ← Fin.sum_univ_fun_getElem, ← Fin.sum_univ_fun_getElem,
    ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hiff : M.IsFlexibleSeg p (⟨j, k⟩ : M.Seg i) ↔
      (((M.util i j).segs[k.1]).1 : ℝ) = M.flexBpb p i * p j := by
    simp only [FisherMarket.IsFlexibleSeg, FisherMarket.segBpb, FisherMarket.segSlope,
      List.get_eq_getElem]
    exact div_eq_iff (ne_of_gt hp)
  simp only [FisherMarket.segAmount, List.get_eq_getElem]
  set sl := (((M.util i j).segs[k.1]).1 : ℝ)
  set r := M.flexBpb p i
  by_cases h1 : sl = r * p j
  · rw [if_pos (hiff.mpr h1), if_pos (le_of_eq h1.symm), if_neg (not_lt.mpr (le_of_eq h1))]
    ring
  · rw [if_neg (fun h' => h1 (hiff.mp h'))]
    rcases lt_or_gt_of_ne h1 with h2 | h2
    · rw [if_neg (not_le.mpr h2), if_neg (not_lt.mpr h2.le)]; ring
    · rw [if_pos h2.le, if_pos h2]; ring

lemma aux_lpo_spent_eq {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) :
    M.spent p i = ∑ j, p j * M.forcedAmount p i j := by
  classical
  unfold FisherMarket.spent FisherMarket.forcedAmount
  rw [Finset.sum_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [FisherMarket.segValue]
  split_ifs <;> ring

lemma aux_lpo_spentLP_self {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) :
    M.spentLP p i p = M.spent p i := rfl

lemma aux_lpo_valueAbove_eq {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ)
    (hp : ∀ j, 0 < p j) (i : Fin n) (r : ℝ) :
    ∑ s ∈ Finset.univ.filter (fun s : M.Seg i => r ≤ M.segBpb p s), M.segValue p s =
      ∑ j, p j * aux_lpo_Age (M.util i j).segs (r * p j) := by
  classical
  rw [Finset.sum_filter, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  unfold aux_lpo_Age
  rw [← Fin.sum_univ_fun_getElem, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hiff : r ≤ M.segBpb p (⟨j, k⟩ : M.Seg i) ↔
      r * p j ≤ (((M.util i j).segs[k.1]).1 : ℝ) := by
    simp only [FisherMarket.segBpb, FisherMarket.segSlope, List.get_eq_getElem]
    exact le_div_iff₀ (hp j)
  simp only [FisherMarket.segValue, FisherMarket.segAmount, List.get_eq_getElem]
  by_cases h : r * p j ≤ (((M.util i j).segs[k.1]).1 : ℝ)
  · rw [if_pos (hiff.mpr h), if_pos h]; ring
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]; ring

/-! Facts about `flexBpb`. -/

lemma aux_lpo_tail_le_flex {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n)
    (j : Fin g) : M.pieceBpb p (⟨j, none⟩ : M.Piece i) ≤ M.flexBpb p i := by
  unfold FisherMarket.flexBpb
  apply le_csSup
  · exact ((Set.finite_range _).subset (fun r hr => hr.1)).bddAbove
  · exact ⟨⟨_, rfl⟩, Or.inl ⟨j, le_rfl⟩⟩

lemma aux_lpo_flex_mem {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n)
    (j : Fin g) : M.ValueAboveExceeds p i (M.flexBpb p i) := by
  have hmem := Set.Nonempty.csSup_mem
    (s := {r | r ∈ Set.range (fun s : M.Piece i => M.pieceBpb p s) ∧ M.ValueAboveExceeds p i r})
    ⟨_, ⟨⟨_, rfl⟩, Or.inl ⟨j, le_rfl⟩⟩⟩ ((Set.finite_range _).subset (fun r hr => hr.1))
  exact hmem.2

lemma aux_lpo_spent_le {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ) (i : Fin n) :
    M.spent p i ≤ M.budget i := by
  classical
  by_contra hlt
  push Not at hlt
  have hb : (0:ℝ) < M.budget i := by exact_mod_cast M.budget_pos i
  unfold FisherMarket.spent at hlt
  set F := Finset.univ.filter (fun s : M.Seg i => M.IsForcedSeg p s) with hF
  have hFne : F.Nonempty := by
    apply Finset.nonempty_of_sum_ne_zero (f := fun s => M.segValue p s)
    intro h0
    rw [h0] at hlt
    linarith
  obtain ⟨s0, hs0, hmin⟩ := Finset.exists_min_image F (fun s => M.segBpb p s) hFne
  have hr1 : M.flexBpb p i < M.segBpb p s0 := (Finset.mem_filter.mp hs0).2
  have hmemS : M.segBpb p s0 ∈
      {r | r ∈ Set.range (fun s : M.Piece i => M.pieceBpb p s) ∧ M.ValueAboveExceeds p i r} := by
    refine ⟨⟨⟨s0.1, some s0.2⟩, rfl⟩,
      Or.inr (lt_of_lt_of_eq hlt (Finset.sum_congr ?_ (fun _ _ => rfl)))⟩
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hF]
    constructor
    · intro h
      exact hmin s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · intro h
      exact lt_of_lt_of_le hr1 h
  have := le_csSup ((Set.finite_range (fun s : M.Piece i => M.pieceBpb p s)).subset
    (fun r hr => hr.1)).bddAbove hmemS
  have h2 : M.segBpb p s0 ≤ M.flexBpb p i := this
  linarith

/-! The exchange argument. -/

lemma aux_lpo_sum_two {g : ℕ} (G : Fin g → ℝ → ℝ) (u v : Fin g → ℝ) (j j' : Fin g)
    (hne : j ≠ j') (h : ∀ k, k ≠ j → k ≠ j' → u k = v k) :
    ∑ k, G k (u k) - ∑ k, G k (v k) = (G j (u j) - G j (v j)) + (G j' (u j') - G j' (v j')) := by
  rw [← Finset.sum_sub_distrib]
  have hpair := Finset.sum_pair (f := fun k => G k (u k) - G k (v k)) hne
  rw [← hpair]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  rw [h k hk.1 hk.2, sub_self]

lemma aux_lpo_exchange {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ) (hp : ∀ j, 0 < p j)
    (i : Fin n) (x : Fin g → ℝ) (hx : M.IsOptimalBundle p i x) (j j' : Fin g) (hne : j ≠ j')
    (δ : ℝ) (hδ : 0 ≤ δ) (hxj : 0 ≤ x j - δ / p j) :
    (M.util i j').eval (x j' + δ / p j') - (M.util i j').eval (x j') ≤
      (M.util i j).eval (x j) - (M.util i j).eval (x j - δ / p j) := by
  obtain ⟨hx0, hxb, hxopt⟩ := hx
  set y := Function.update (Function.update x j (x j - δ / p j)) j' (x j' + δ / p j') with hy
  have hyj : y j = x j - δ / p j := by simp [hy, hne]
  have hyj' : y j' = x j' + δ / p j' := by simp [hy]
  have hyk : ∀ k, k ≠ j → k ≠ j' → y k = x k := by
    intro k h1 h2; simp [hy, h1, h2]
  have hy0 : ∀ k, 0 ≤ y k := by
    intro k
    by_cases h1 : k = j
    · subst h1; rw [hyj]; exact hxj
    by_cases h2 : k = j'
    · subst h2; rw [hyj']
      have := hx0 k
      have : 0 ≤ δ / p k := div_nonneg hδ (le_of_lt (hp k))
      linarith
    rw [hyk k h1 h2]; exact hx0 k
  have hbud : ∑ k, p k * y k = ∑ k, p k * x k := by
    have := aux_lpo_sum_two (fun k t => p k * t) y x j j' hne hyk
    rw [hyj, hyj'] at this
    have hpj : p j ≠ 0 := (hp j).ne'
    have hpj' : p j' ≠ 0 := (hp j').ne'
    have e1 : p j * (x j - δ / p j) - p j * x j = -δ := by
      field_simp; ring
    have e2 : p j' * (x j' + δ / p j') - p j' * x j' = δ := by
      field_simp; ring
    linarith
  have hle := hxopt y hy0 (by rw [hbud]; exact hxb)
  have := aux_lpo_sum_two (fun k t => (M.util i k).eval t) y x j j' hne hyk
  simp only [FisherMarket.utility] at hle
  rw [hyj, hyj'] at this
  linarith

lemma aux_lpo_mul_div (r q δ : ℝ) (hq : q ≠ 0) : r * q * (δ / q) = r * δ := by
  field_simp

lemma aux_lpo_core {n g : ℕ} (M : FisherMarket n g) (p : Fin g → ℝ) (hp : ∀ j, 0 < p j)
    (i : Fin n) (x : Fin g → ℝ) (hx : M.IsOptimalBundle p i x)
    (hspend : ∑ j, p j * x j = M.budget i) :
    (∀ j, aux_lpo_Agt (M.util i j).segs (M.flexBpb p i * p j) ≤ x j) ∧
    (∀ j, ¬ M.IsFlexibleTail p i j →
      x j ≤ aux_lpo_Age (M.util i j).segs (M.flexBpb p i * p j)) := by
  set r := M.flexBpb p i with hr
  have htail : ∀ j, ((M.util i j).tail : ℝ) ≤ r * p j := by
    intro j
    have h1 : ((M.util i j).tail : ℝ) / p j ≤ r := aux_lpo_tail_le_flex M p i j
    exact (div_le_iff₀ (hp j)).mp h1
  have hr0 : ∀ j : Fin g, 0 ≤ r := by
    intro j
    have h1 : ((M.util i j).tail : ℝ) / p j ≤ r := aux_lpo_tail_le_flex M p i j
    have : (0:ℝ) ≤ ((M.util i j).tail : ℝ) / p j :=
      div_nonneg (by exact_mod_cast (M.util i j).tail_nonneg) (le_of_lt (hp j))
    linarith
  have hamt : ∀ j, ∀ s ∈ (M.util i j).segs, (0:ℚ) ≤ s.2 := fun j => aux_lpo_segs_amt _
  constructor
  · intro j
    by_contra hlt
    push Not at hlt
    by_cases hex : ∃ j', aux_lpo_Agt (M.util i j').segs (r * p j') < x j'
    · obtain ⟨j', hj'⟩ := hex
      have hne : j' ≠ j := by rintro rfl; linarith
      set A := aux_lpo_Agt (M.util i j).segs (r * p j) with hA
      set A' := aux_lpo_Agt (M.util i j').segs (r * p j') with hA'
      set δ := min (p j * (A - x j)) (p j' * (x j' - A')) with hδ
      have hδpos : 0 < δ := lt_min (mul_pos (hp j) (by linarith)) (mul_pos (hp j') (by linarith))
      have hδ1 : δ / p j ≤ A - x j := by
        rw [div_le_iff₀ (hp j)]
        have := min_le_left (p j * (A - x j)) (p j' * (x j' - A'))
        linarith
      have hδ2 : δ / p j' ≤ x j' - A' := by
        rw [div_le_iff₀ (hp j')]
        have := min_le_right (p j * (A - x j)) (p j' * (x j' - A'))
        linarith
      have hA'0 : 0 ≤ A' := aux_lpo_Agt_nonneg _ (hamt j') _
      have hd1 := div_pos hδpos (hp j)
      have hd2 := div_pos hδpos (hp j')
      have hexc := aux_lpo_exchange M p hp i x hx j' j hne δ hδpos.le (by linarith)
      have hgain := aux_lpo_E1 (M.util i j) (r * p j) (htail j) (x j) (x j + δ / p j)
        (hx.1 j) (by linarith) (by linarith)
      have hloss := aux_lpo_E2 (M.util i j') (r * p j') (mul_nonneg (hr0 j) (hp j').le)
        (htail j') (x j' - δ / p j') (x j') (by linarith) (by linarith)
      have e1 : r * p j * (x j + δ / p j - x j) = r * δ := by
        rw [show x j + δ / p j - x j = δ / p j by ring]
        exact aux_lpo_mul_div r (p j) δ (hp j).ne'
      have e2 : r * p j' * (x j' - (x j' - δ / p j')) = r * δ := by
        rw [show x j' - (x j' - δ / p j') = δ / p j' by ring]
        exact aux_lpo_mul_div r (p j') δ (hp j').ne'
      linarith
    · push Not at hex
      have h1 : ∑ k, p k * x k < ∑ k, p k * aux_lpo_Agt (M.util i k).segs (r * p k) :=
        Finset.sum_lt_sum (fun k _ => mul_le_mul_of_nonneg_left (hex k) (hp k).le)
          ⟨j, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt (hp j)⟩
      have h2 : M.spent p i = ∑ k, p k * aux_lpo_Agt (M.util i k).segs (r * p k) := by
        rw [aux_lpo_spent_eq]
        apply Finset.sum_congr rfl
        intro k _
        rw [aux_lpo_forcedAmount_eq M p i k (hp k)]
      have h3 := aux_lpo_spent_le M p i
      linarith
  · intro j hj
    by_contra hlt
    push Not at hlt
    have htj : ((M.util i j).tail : ℝ) < r * p j := by
      rcases lt_or_eq_of_le (htail j) with h | h
      · exact h
      · exfalso; apply hj
        show ((M.util i j).tail : ℝ) / p j = r
        rw [h, div_eq_iff (hp j).ne']
    set Aj := aux_lpo_Age (M.util i j).segs (r * p j) with hAj
    have hAj0 : 0 ≤ Aj := aux_lpo_Age_nonneg _ (hamt j) _
    by_cases hex : ∃ j', M.IsFlexibleTail p i j' ∨
        x j' < aux_lpo_Age (M.util i j').segs (r * p j')
    · obtain ⟨j', hj'⟩ := hex
      have hne : j ≠ j' := by
        rintro rfl
        rcases hj' with h | h
        · exact hj h
        · linarith
      set Aj' := aux_lpo_Age (M.util i j').segs (r * p j') with hAj'
      have key : ∀ δ : ℝ, 0 < δ → δ / p j ≤ x j - Aj →
          (x j' + δ / p j' ≤ Aj' ∨ ((M.util i j').tail : ℝ) = r * p j') → False := by
        intro δ hδ h1 h2
        have hd1 := div_pos hδ (hp j)
        have hd2 := div_pos hδ (hp j')
        have hexc := aux_lpo_exchange M p hp i x hx j j' hne δ hδ.le (by linarith)
        have hloss := aux_lpo_E4 (M.util i j) (r * p j) htj (x j - δ / p j) (x j)
          (by linarith) (by linarith)
        have hgain := aux_lpo_E3 (M.util i j') (r * p j') (x j') (x j' + δ / p j')
          (hx.1 j') (by linarith) h2
        have e1 : r * p j * (x j - (x j - δ / p j)) = r * δ := by
          rw [show x j - (x j - δ / p j) = δ / p j by ring]
          exact aux_lpo_mul_div r (p j) δ (hp j).ne'
        have e2 : r * p j' * (x j' + δ / p j' - x j') = r * δ := by
          rw [show x j' + δ / p j' - x j' = δ / p j' by ring]
          exact aux_lpo_mul_div r (p j') δ (hp j').ne'
        linarith
      rcases hj' with hflex | hlt'
      · have htf : ((M.util i j').tail : ℝ) = r * p j' := by
          have h0 : ((M.util i j').tail : ℝ) / p j' = r := hflex
          rw [div_eq_iff (ne_of_gt (hp j'))] at h0
          exact h0
        refine key (p j * (x j - Aj)) (mul_pos (hp j) (by linarith)) ?_ (Or.inr htf)
        rw [div_le_iff₀ (hp j)]; linarith
      · set δ := min (p j * (x j - Aj)) (p j' * (Aj' - x j')) with hδ
        have hδpos : 0 < δ :=
          lt_min (mul_pos (hp j) (by linarith)) (mul_pos (hp j') (by linarith))
        refine key δ hδpos ?_ (Or.inl ?_)
        · rw [div_le_iff₀ (hp j)]
          have := min_le_left (p j * (x j - Aj)) (p j' * (Aj' - x j'))
          linarith
        · have : δ / p j' ≤ Aj' - x j' := by
            rw [div_le_iff₀ (hp j')]
            have := min_le_right (p j * (x j - Aj)) (p j' * (Aj' - x j'))
            linarith
          linarith
    · push Not at hex
      rcases aux_lpo_flex_mem M p i j with ⟨j', hj'⟩ | hlt2
      · exact (hex j').1 (le_antisymm (aux_lpo_tail_le_flex M p i j') hj')
      · rw [aux_lpo_valueAbove_eq M p hp i] at hlt2
        have h1 : ∑ k, p k * aux_lpo_Age (M.util i k).segs (r * p k) < ∑ k, p k * x k :=
          Finset.sum_lt_sum (fun k _ => mul_le_mul_of_nonneg_left (hex k).2 (hp k).le)
            ⟨j, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt (hp j)⟩
        have h2 := hx.2.1
        linarith

end PLCMarkets.Rationality

open PLCMarkets.Rationality

theorem solution {n g : ℕ} (M : FisherMarket n g) (p' : Fin g → ℝ)
    (hp' : M.IsEquilibrium p')
    (hpos : ∀ j, 0 < p' j)
    (hsum : ∑ j, p' j = ∑ i, (M.budget i : ℝ)) :
    ∃ z : FisherMarket.LPPoint n g, z.p = p' ∧ M.IsLPOptimal p' z ∧
      M.lpObjective p' z = ∑ i, (M.budget i : ℝ) := by
  obtain ⟨_, x, hopt, hclear⟩ := hp'
  have hspend : ∀ i, ∑ j, p' j * x i j = M.budget i := by
    have hle : ∀ i, ∑ j, p' j * x i j ≤ M.budget i := fun i => (hopt i).2.1
    have htot : ∑ i, ∑ j, p' j * x i j = ∑ i, (M.budget i : ℝ) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hclear, mul_one]
      exact hsum
    have h0 : ∀ i ∈ Finset.univ, (M.budget i : ℝ) - ∑ j, p' j * x i j = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (hle i))).mp
      rw [Finset.sum_sub_distrib, htot, sub_self]
    intro i
    linarith [h0 i (Finset.mem_univ _)]
  have hcore := fun i => aux_lpo_core M p' hpos i (x i) (hopt i) (hspend i)
  have hFA : ∀ i j, M.forcedAmount p' i j =
      aux_lpo_Agt (M.util i j).segs (M.flexBpb p' i * p' j) :=
    fun i j => aux_lpo_forcedAmount_eq M p' i j (hpos j)
  set fm : Fin g → Fin n → ℝ := fun j i => p' j * (x i j - M.forcedAmount p' i j) with hfm
  have hfm0 : ∀ j i, 0 ≤ fm j i := by
    intro j i
    simp only [hfm]
    rw [hFA]
    exact mul_nonneg (hpos j).le (sub_nonneg.mpr ((hcore i).1 j))
  have hsnk : ∀ i, ∑ j, fm j i = M.unspent p' i := by
    intro i
    simp only [hfm, FisherMarket.unspent, mul_sub, Finset.sum_sub_distrib, hspend i]
    rw [aux_lpo_spent_eq]
  have hsrc : ∀ j, ∑ i, fm j i = M.unsold p' j * p' j := by
    intro j
    simp only [hfm, FisherMarket.unsold, FisherMarket.forced, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hclear j]
    ring
  have hobjz : ∑ j, ∑ i, fm j i + ∑ i, M.spentLP p' i p' = ∑ i, (M.budget i : ℝ) := by
    rw [Finset.sum_comm]
    simp only [hsnk, aux_lpo_spentLP_self, FisherMarket.unspent, ← Finset.sum_add_distrib,
      sub_add_cancel]
  refine ⟨⟨p', fun j => ∑ i, fm j i, fm, fun i => ∑ j, fm j i, ∑ j, ∑ i, fm j i⟩, rfl,
    ⟨?_, ?_⟩, hobjz⟩
  · refine ⟨fun j => (hsrc j).le, ?_, ?_, rfl, fun j => rfl, fun i => rfl,
      (show ∑ i, ∑ j, fm j i = ∑ j, ∑ i, fm j i from Finset.sum_comm),
      ?_, ?_, ?_, ?_, ?_, hsum,
      fun j => show (0:ℝ) ≤ ∑ i, fm j i from Finset.sum_nonneg (fun i _ => hfm0 j i), hfm0,
      fun i => show (0:ℝ) ≤ ∑ j, fm j i from Finset.sum_nonneg (fun j _ => hfm0 j i),
      (show (0:ℝ) ≤ ∑ j, ∑ i, fm j i from
        Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun i _ => hfm0 j i))),
      fun j => (hpos j).le⟩
    · intro j i hj
      show fm j i ≤ M.flexCapLP p' j i p'
      rw [aux_lpo_flexCapLP_eq M p' i j (hpos j)]
      simp only [hfm]
      rw [hFA]
      exact mul_le_mul_of_nonneg_left (by linarith [(hcore i).2 j hj]) (hpos j).le
    · intro i
      show ∑ j, fm j i ≤ M.unspentLP p' i p'
      rw [hsnk]
      exact le_of_eq (by simp only [FisherMarket.unspentLP, aux_lpo_spentLP_self,
        FisherMarket.unspent])
    · intro i σ τ hσ hτ
      have h := hσ.trans hτ.symm
      simp only [FisherMarket.pieceBpb] at h
      exact (div_eq_div_iff (hpos _).ne' (hpos _).ne').mp h
    · intro i σ τ hσ hτ
      have h := hσ ▸ hτ
      simp only [FisherMarket.pieceBpb] at h
      exact ((div_lt_div_iff₀ (hpos _) (hpos _)).mp h).le
    · intro i σ τ hσ hτ
      have h := hσ ▸ hτ
      simp only [FisherMarket.pieceBpb] at h
      exact ((div_lt_div_iff₀ (hpos _) (hpos _)).mp h).le
    · intro i
      show 0 ≤ M.unspentLP p' i p'
      have : M.unspentLP p' i p' = M.unspent p' i := by
        simp only [FisherMarket.unspentLP, aux_lpo_spentLP_self, FisherMarket.unspent]
      rw [this, ← hsnk]
      exact Finset.sum_nonneg (fun j _ => hfm0 j i)
    · intro j
      have h1 : 0 ≤ M.unsold p' j * p' j := by
        rw [← hsrc]; exact Finset.sum_nonneg (fun i _ => hfm0 j i)
      by_contra h2
      push Not at h2
      have := mul_neg_of_neg_of_pos h2 (hpos j)
      linarith
  · intro w hw
    obtain ⟨_, _, hw3, _, _, _, hw7, _⟩ := hw
    show w.fts + ∑ i, M.spentLP p' i w.p ≤ ∑ j, ∑ i, fm j i + ∑ i, M.spentLP p' i p'
    rw [hobjz, ← hw7, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have := hw3 i
    simp only [FisherMarket.unspentLP] at this
    linarith
