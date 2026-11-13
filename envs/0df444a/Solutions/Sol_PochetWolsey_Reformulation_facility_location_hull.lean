-- Prove2me | solution 1 for PochetWolsey.Reformulation.facility_location_hull
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T15:45:06.24493+00:00
-- url     : https://prove2.me/submissions/1d736b67-a8e9-428f-9136-8df26bae2e40

import Mathlib

set_option autoImplicit false

namespace FLH

open Finset

/-- The lot-sizing set X of the target (same text as the `let X`). -/
def Xs (n : ℕ) (d : Fin n → ℝ) (a : ℝ) :
    Set ((Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
  {z | z.2.1 0 = a ∧ z.2.1 (Fin.last n) = 0 ∧
        (∀ k, 0 ≤ z.2.1 k) ∧
        (∀ i, 0 ≤ z.1 i ∧ (z.2.2 i = 0 ∨ z.2.2 i = 1) ∧
          z.2.1 i.castSucc + z.1 i = d i + z.2.1 i.succ ∧
          z.1 i ≤ (∑ t ∈ Finset.univ.filter (fun t => i ≤ t), d t) * z.2.2 i)}

/-- The multi-commodity relaxation Q of the target (same text as the `let Q`). -/
def Qp (n : ℕ) (d : Fin n → ℝ) (a : ℝ) (w : Fin n → Fin n → ℝ)
    (v : Fin (n + 1) → Fin n → ℝ) (y : Fin n → ℝ) : Prop :=
  (∀ i t, 0 ≤ w i t) ∧ (∀ k t, 0 ≤ v k t) ∧
      (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
      (∀ i t, t < i → w i t = 0) ∧
      (∀ k t, t.val < k.val → v k t = 0) ∧
      (∀ t, v 0 t = if t.val = 0 then a else 0) ∧
      (∀ i t, i ≤ t →
        v i.castSucc t + w i t = (if i = t then d t else 0) + v i.succ t) ∧
      (∀ i t, i ≤ t → w i t ≤ (d t - (if t.val = 0 then a else 0)) * y i)

def proj {n : ℕ} (w : Fin n → Fin n → ℝ) (v : Fin (n + 1) → Fin n → ℝ) (y : Fin n → ℝ) :
    (Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ) :=
  ((fun i => ∑ t, w i t), (fun k => ∑ t, v k t), y)

/-- Every Q-point projects onto a point satisfying all constraints of X except
binarity of y.  With binary y the projection lies in X. -/
theorem proj_mem_X_of_binary (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t)
    (a : ℝ) (ha : 0 ≤ a) (w : Fin n → Fin n → ℝ) (v : Fin (n + 1) → Fin n → ℝ)
    (y : Fin n → ℝ) (hQ : Qp n d a w v y) (hbin : ∀ i, y i = 0 ∨ y i = 1) :
    proj w v y ∈ Xs n d a := by
  obtain ⟨hw, hv, hy, hwl, hvl, hv0, hbal, hcap⟩ := hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ∑ t, v 0 t = a
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · rw [hv0]; simp
    · intro b _ hb
      rw [hv0, if_neg]
      intro h0; exact hb (Fin.ext h0)
    · intro h; exact absurd (Finset.mem_univ _) h
  · show ∑ t, v (Fin.last n) t = 0
    exact Finset.sum_eq_zero (fun t _ => hvl _ _ (by simp))
  · intro k
    show 0 ≤ ∑ t, v k t
    exact Finset.sum_nonneg (fun t _ => hv k t)
  · intro i
    refine ⟨show 0 ≤ ∑ t, w i t from Finset.sum_nonneg (fun t _ => hw i t), hbin i, ?_, ?_⟩
    · show ∑ t, v i.castSucc t + ∑ t, w i t = d i + ∑ t, v i.succ t
      have key : ∀ t, v i.castSucc t + w i t = (if i = t then d t else 0) + v i.succ t := by
        intro t
        by_cases hit : i ≤ t
        · exact hbal i t hit
        · have hti : t < i := lt_of_not_ge hit
          have hlt : t.val < i.val := Fin.lt_def.1 hti
          have h1 : v i.castSucc t = 0 := hvl _ _ (by simp only [Fin.val_castSucc]; omega)
          have h2 : v i.succ t = 0 := hvl _ _ (by simp only [Fin.val_succ]; omega)
          rw [h1, h2, hwl i t hti, if_neg (ne_of_gt hti)]
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun t _ => key t),
        Finset.sum_add_distrib, Finset.sum_ite_eq]
      simp
    · show ∑ t, w i t ≤ (∑ t ∈ Finset.univ.filter (fun t => i ≤ t), d t) * y i
      rw [Finset.sum_mul]
      calc ∑ t, w i t = ∑ t ∈ Finset.univ.filter (fun t => i ≤ t), w i t := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl (fun t _ => ?_)
            split_ifs with h
            · rfl
            · exact hwl i t (lt_of_not_ge h)
        _ ≤ ∑ t ∈ Finset.univ.filter (fun t => i ≤ t), d t * y i := by
            refine Finset.sum_le_sum (fun t ht => ?_)
            have hit : i ≤ t := (Finset.mem_filter.1 ht).2
            refine (hcap i t hit).trans ?_
            apply mul_le_mul_of_nonneg_right _ (hy i).1
            split_ifs <;> linarith

/-! ## Child statements of the decomposition (see scratch/decomp/28ebc150.plan.md). -/

/-- C1 (FIFO lift): every point of X is the projection of a Q-point. -/
def C1_lift : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (d : Fin n → ℝ), (∀ t, 0 ≤ d t) → ∀ (a : ℝ), 0 ≤ a →
    (∀ t : Fin n, t.val = 0 → a ≤ d t) →
    ∀ z ∈ Xs n d a, ∃ w v y, Qp n d a w v y ∧ z = proj w v y

/-- C2a (nested facility-location rounding, Krarup-Bilde integrality): any fractional
assignment with fractional opening can be replaced by an integral opening `S` and an
assignment using only open facilities, at no larger cost. -/
def C2a_round : Prop :=
  ∀ (n : ℕ) (D : Fin n → ℝ), (∀ t, 0 ≤ D t) →
    ∀ (f : Fin n → Fin n → ℝ) (y : Fin n → ℝ),
    (∀ i t, 0 ≤ f i t) → (∀ i t, t < i → f i t = 0) → (∀ t, ∑ i, f i t = D t) →
    (∀ i t, f i t ≤ D t * y i) → (∀ i, 0 ≤ y i ∧ y i ≤ 1) →
    ∀ (φ γ : Fin n → ℝ),
    ∃ (S : Finset (Fin n)) (g : Fin n → Fin n → ℝ),
      (∀ i t, 0 ≤ g i t) ∧ (∀ i t, t < i → g i t = 0) ∧ (∀ t, ∑ i, g i t = D t) ∧
      (∀ i t, i ∉ S → g i t = 0) ∧
      ∑ i, φ i * ∑ t, g i t + ∑ i ∈ S, γ i ≤ ∑ i, φ i * ∑ t, f i t + ∑ i, γ i * y i

/-- C2 (LP integrality in X-form): for every objective linear in (x, y). -/
def C2_round : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (d : Fin n → ℝ), (∀ t, 0 ≤ d t) → ∀ (a : ℝ), 0 ≤ a →
    (∀ t : Fin n, t.val = 0 → a ≤ d t) →
    ∀ (φ γ : Fin n → ℝ) w v y, Qp n d a w v y →
      ∃ z ∈ Xs n d a, ∑ i, (φ i * z.1 i + γ i * z.2.2 i) ≤
        ∑ i, (φ i * (proj w v y).1 i + γ i * y i)

lemma tele (n : ℕ) (g : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (g i.succ - g i.castSucc) = g (Fin.last n) - g 0 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.succ_castSucc]
    have := ih (fun k => g k.castSucc)
    rw [this, Fin.succ_last, Fin.castSucc_zero]
    ring

/-- Termwise balance of a Q-point, valid for all `i` (not only `i ≤ t`). -/
lemma bal_all (n : ℕ) (d : Fin n → ℝ) (a : ℝ) (w : Fin n → Fin n → ℝ)
    (v : Fin (n + 1) → Fin n → ℝ) (y : Fin n → ℝ) (hQ : Qp n d a w v y) (i t : Fin n) :
    v i.castSucc t + w i t = (if i = t then d t else 0) + v i.succ t := by
  obtain ⟨hw, hv, hy, hwl, hvl, hv0, hbal, hcap⟩ := hQ
  by_cases hit : i ≤ t
  · exact hbal i t hit
  · have hti : t < i := lt_of_not_ge hit
    have hlt : t.val < i.val := Fin.lt_def.1 hti
    have h1 : v i.castSucc t = 0 := hvl _ _ (by simp only [Fin.val_castSucc]; omega)
    have h2 : v i.succ t = 0 := hvl _ _ (by simp only [Fin.val_succ]; omega)
    rw [h1, h2, hwl i t hti, if_neg (ne_of_gt hti)]

/-- Demand-row identity of a Q-point: `∑_i w i t = d t - a·[t = 0]`. -/
lemma demand_row (n : ℕ) (d : Fin n → ℝ) (a : ℝ) (w : Fin n → Fin n → ℝ)
    (v : Fin (n + 1) → Fin n → ℝ) (y : Fin n → ℝ) (hQ : Qp n d a w v y) (t : Fin n) :
    ∑ i, w i t = d t - (if t.val = 0 then a else 0) := by
  have hT := tele n (fun k => v k t)
  have hl : v (Fin.last n) t = 0 := hQ.2.2.2.2.1 _ _ (by simp)
  have h0 := hQ.2.2.2.2.2.1 t
  have hs : ∀ i, v i.succ t - v i.castSucc t = w i t - (if i = t then d t else 0) := by
    intro i; have := bal_all n d a w v y hQ i t; linarith
  rw [Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_sub_distrib, Finset.sum_ite_eq'] at hT
  simp only [Finset.mem_univ, if_true] at hT
  rw [hl, h0] at hT
  linarith

/-- C2 follows from the combinatorial rounding C2a. -/
theorem C2_of_C2a (H : C2a_round) : C2_round := by
  intro n hn d hd a ha haf φ γ w v y hQ
  set D : Fin n → ℝ := fun t => d t - (if t.val = 0 then a else 0) with hDdef
  have hD : ∀ t, 0 ≤ D t := by
    intro t; simp only [hDdef]; split_ifs with h
    · linarith [haf t h]
    · linarith [hd t]
  obtain ⟨hw, hv, hy, hwl, hvl, hv0, hbal, hcap⟩ := hQ
  have hsum : ∀ t, ∑ i, w i t = D t := fun t =>
    demand_row n d a w v y ⟨hw, hv, hy, hwl, hvl, hv0, hbal, hcap⟩ t
  have hcap' : ∀ i t, w i t ≤ D t * y i := by
    intro i t
    by_cases hit : i ≤ t
    · exact hcap i t hit
    · rw [hwl i t (lt_of_not_ge hit)]; exact mul_nonneg (hD t) (hy i).1
  obtain ⟨S, g, hg0, hgl, hgs, hgS, hcost⟩ := H n D hD w y hw hwl hsum hcap' hy φ γ
  -- the integral Q-point
  let y' : Fin n → ℝ := fun i => if i ∈ S then 1 else 0
  let v' : Fin (n + 1) → Fin n → ℝ := fun k t =>
    if k.val ≤ t.val then (if t.val = 0 then a else 0) +
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < k.val), g j t else 0
  have hQ' : Qp n d a g v' y' := by
    refine ⟨hg0, ?_, ?_, hgl, ?_, ?_, ?_, ?_⟩
    · intro k t
      simp only [v']
      split_ifs
      · exact add_nonneg ha (Finset.sum_nonneg (fun j _ => hg0 j t))
      · exact add_nonneg le_rfl (Finset.sum_nonneg (fun j _ => hg0 j t))
      · exact le_rfl
    · intro i; simp only [y']; split_ifs <;> norm_num
    · intro k t hkt
      simp only [v']
      rw [if_neg (by omega)]
    · intro t
      simp only [v', Fin.val_zero, Nat.zero_le, if_true]
      simp
    · intro i t hit
      have hit' : i.val ≤ t.val := Fin.le_def.1 hit
      simp only [v', Fin.val_castSucc, Fin.val_succ]
      rw [if_pos hit']
      have hsplit : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val + 1), g j t =
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val), g j t + g i t := by
        have hgi : g i t = ∑ j, if j = i then g j t else 0 := by simp
        rw [Finset.sum_filter, Finset.sum_filter, hgi, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hji : j = i
        · subst hji; simp
        · have : j.val ≠ i.val := fun h => hji (Fin.ext h)
          simp only [if_neg hji, add_zero]
          by_cases hlt : j.val < i.val
          · rw [if_pos hlt, if_pos (by omega)]
          · rw [if_neg hlt, if_neg (by omega)]
      by_cases hieq : i = t
      · subst hieq
        rw [if_neg (show ¬ (i.val + 1 ≤ i.val) by omega), if_pos rfl]
        have hall : ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val < i.val + 1), g j i = D i := by
          rw [← hgs i, Finset.sum_filter]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          split_ifs with hj
          · rfl
          · exact (hgl j i (Fin.lt_def.2 (by omega))).symm
        have := hall; rw [hsplit] at this
        simp only [hDdef] at this
        linarith
      · have hlt : i.val < t.val := lt_of_le_of_ne hit' (fun h => hieq (Fin.ext h))
        rw [if_pos (show i.val + 1 ≤ t.val by omega), if_neg hieq, hsplit]
        ring
    · intro i t _
      by_cases hiS : i ∈ S
      · simp only [y', if_pos hiS, mul_one]
        have := hgs t
        simp only [hDdef] at this
        rw [← this]
        exact Finset.single_le_sum (fun j _ => hg0 j t) (Finset.mem_univ i)
      · simp only [y', if_neg hiS, mul_zero]
        rw [hgS i t hiS]
  have hbin : ∀ i, y' i = 0 ∨ y' i = 1 := by
    intro i; simp only [y']; split_ifs <;> simp
  refine ⟨proj g v' y', proj_mem_X_of_binary n hn d hd a ha g v' y' hQ' hbin, ?_⟩
  simp only [proj, y']
  have e1 : ∑ i, (φ i * ∑ t, g i t + γ i * (if i ∈ S then (1:ℝ) else 0)) =
      ∑ i, φ i * ∑ t, g i t + ∑ i ∈ S, γ i := by
    rw [Finset.sum_add_distrib]
    congr 1
    simp [mul_ite, Finset.sum_ite_mem]
  rw [e1, Finset.sum_add_distrib]
  exact hcost

/-! ## C1: FIFO lift -/

/-- Cumulative demand before period `k`. -/
noncomputable def Dc {n : ℕ} (d : Fin n → ℝ) (k : Fin (n + 1)) : ℝ :=
  ∑ u : Fin n, if u.val < k.val then d u else 0

lemma Dc_zero {n : ℕ} (d : Fin n → ℝ) : Dc d 0 = 0 := by simp [Dc]

lemma Dc_succ {n : ℕ} (d : Fin n → ℝ) (t : Fin n) :
    Dc d t.succ = Dc d t.castSucc + d t := by
  unfold Dc
  have hgi : d t = ∑ j, if j = t then d j else 0 := by simp
  rw [hgi, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Fin.val_succ, Fin.val_castSucc]
  by_cases hji : j = t
  · subst hji; simp
  · have : j.val ≠ t.val := fun h => hji (Fin.ext h)
    simp only [if_neg hji, add_zero]
    by_cases hlt : j.val < t.val
    · rw [if_pos hlt, if_pos (show j.val < t.val + 1 by omega)]
    · rw [if_neg hlt, if_neg (show ¬ (j.val < t.val + 1) by omega)]

lemma Dc_mono {n : ℕ} (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) : Monotone (Dc d) :=
  Fin.monotone_iff_le_succ.2 (fun t => by rw [Dc_succ]; linarith [hd t])

lemma Dc_nonneg {n : ℕ} (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (k : Fin (n + 1)) :
    0 ≤ Dc d k :=
  Finset.sum_nonneg (fun u _ => ite_nonneg (hd u) le_rfl)

lemma Dc_ge_succ {n : ℕ} (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (t : Fin n) (k : Fin (n + 1))
    (h : t.val < k.val) : Dc d t.succ ≤ Dc d k :=
  Dc_mono d hd (Fin.le_def.2 (by simp only [Fin.val_succ]; omega))

/-- Overlap of `[0, z]` with the demand interval of period `t`. -/
noncomputable def ov {n : ℕ} (d : Fin n → ℝ) (z : ℝ) (t : Fin n) : ℝ :=
  min z (Dc d t.succ) - min z (Dc d t.castSucc)

lemma ov_mono {n : ℕ} (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (t : Fin n) {z z' : ℝ}
    (h : z ≤ z') : ov d z t ≤ ov d z' t := by
  have hLH := Dc_succ d t
  have := hd t
  unfold ov
  simp only [min_def]; split_ifs <;> linarith

lemma ov_nonneg {n : ℕ} (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (z : ℝ) (t : Fin n) :
    0 ≤ ov d z t := by
  have hLH := Dc_succ d t
  have := hd t
  unfold ov
  simp only [min_def]; split_ifs <;> linarith

lemma ov_le {n : ℕ} (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (z : ℝ) (t : Fin n) :
    ov d z t ≤ d t := by
  have hLH := Dc_succ d t
  have := hd t
  unfold ov
  simp only [min_def]; split_ifs <;> linarith

lemma ov_top {n : ℕ} (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (t : Fin n) {z : ℝ}
    (h : Dc d t.succ ≤ z) : ov d z t = d t := by
  have hLH := Dc_succ d t
  have := hd t
  unfold ov
  rw [min_eq_right h, min_eq_right (show Dc d t.castSucc ≤ z by linarith)]
  linarith

lemma ov_sum {n : ℕ} (d : Fin n → ℝ) (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ Dc d (Fin.last n)) :
    ∑ t, ov d z t = z := by
  have hT : ∑ t : Fin n, (min z (Dc d t.succ) - min z (Dc d t.castSucc)) =
      min z (Dc d (Fin.last n)) - min z (Dc d 0) := tele n (fun k => min z (Dc d k))
  unfold ov
  rw [hT, Dc_zero, min_eq_left h1, min_eq_right h0]
  ring

lemma ov_a_zero {n : ℕ} (d : Fin n → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (haf : ∀ t : Fin n, t.val = 0 → a ≤ d t) (t : Fin n) (ht : t.val = 0) : ov d a t = a := by
  have hc : t.castSucc = 0 := Fin.ext (by simp [ht])
  have hs := Dc_succ d t
  rw [hc, Dc_zero] at hs
  unfold ov
  rw [hc, Dc_zero, hs, min_eq_left (show a ≤ 0 + d t by linarith [haf t ht]), min_eq_right ha]
  ring

lemma ov_a_pos {n : ℕ} (hn : 0 < n) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (a : ℝ)
    (haf : ∀ t : Fin n, t.val = 0 → a ≤ d t) (t : Fin n) (ht : t.val ≠ 0) :
    ov d a t = 0 := by
  have h0 : a ≤ Dc d t.castSucc := by
    have hpos : 0 < t.val := Nat.pos_of_ne_zero ht
    have hle := Finset.single_le_sum (s := Finset.univ)
      (f := fun u : Fin n => if u.val < t.castSucc.val then d u else 0)
      (fun u _ => ite_nonneg (hd u) le_rfl) (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    have h1 : (if (⟨0, hn⟩ : Fin n).val < t.castSucc.val then d ⟨0, hn⟩ else 0) =
        d ⟨0, hn⟩ := by
      simp [hpos]
    rw [h1] at hle
    exact (haf ⟨0, hn⟩ rfl).trans hle
  have hs := Dc_succ d t
  unfold ov
  rw [min_eq_left h0, min_eq_left (show a ≤ Dc d t.succ by linarith [hd t])]
  ring

/-- C1 holds: the FIFO (first-in first-out) assignment lifts every X point into Q. -/
theorem C1_holds : C1_lift := by
  intro n hn d hd a ha haf z hz
  obtain ⟨hs0, hsl, hsnn, hi⟩ := hz
  set S : Fin (n + 1) → ℝ := fun k => z.2.1 k + Dc d k with hSdef
  have hSsucc : ∀ i : Fin n, S i.succ = S i.castSucc + z.1 i := by
    intro i; simp only [hSdef]; rw [Dc_succ]; linarith [(hi i).2.2.1]
  have hSmono : Monotone S :=
    Fin.monotone_iff_le_succ.2 (fun i => by rw [hSsucc]; linarith [(hi i).1])
  have hSge : ∀ k, Dc d k ≤ S k := fun k => by simp only [hSdef]; linarith [hsnn k]
  have hS0 : S 0 = a := by simp only [hSdef]; rw [hs0, Dc_zero]; ring
  have hSle : ∀ k, S k ≤ Dc d (Fin.last n) := fun k => by
    have := hSmono (Fin.le_last k)
    simp only [hSdef] at this ⊢
    rw [hsl] at this
    linarith
  have hSnn : ∀ k, 0 ≤ S k := fun k => (Dc_nonneg d hd k).trans (hSge k)
  have hcs : ∀ i : Fin n, S i.castSucc ≤ S i.succ := fun i => hSmono Fin.castSucc_lt_succ.le
  refine ⟨fun i t => ov d (S i.succ) t - ov d (S i.castSucc) t,
    fun k t => ov d (S k) t - (if t.val < k.val then d t else 0), z.2.2, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i t
      exact sub_nonneg.2 (ov_mono d hd t (hcs i))
    · intro k t
      show 0 ≤ ov d (S k) t - (if t.val < k.val then d t else 0)
      by_cases hk : t.val < k.val
      · rw [if_pos hk, ov_top d hd t ((Dc_ge_succ d hd t k hk).trans (hSge k))]; simp
      · rw [if_neg hk, sub_zero]; exact ov_nonneg d hd (S k) t
    · intro i
      rcases (hi i).2.1 with h | h <;> rw [h] <;> norm_num
    · intro i t hti
      have hlt : t.val < i.castSucc.val := by
        simp only [Fin.val_castSucc]; exact Fin.lt_def.1 hti
      have h1 := (Dc_ge_succ d hd t _ hlt).trans (hSge i.castSucc)
      have h2 := h1.trans (hcs i)
      show ov d (S i.succ) t - ov d (S i.castSucc) t = 0
      rw [ov_top d hd t h1, ov_top d hd t h2]; ring
    · intro k t hk
      show ov d (S k) t - (if t.val < k.val then d t else 0) = 0
      rw [if_pos hk, ov_top d hd t ((Dc_ge_succ d hd t k hk).trans (hSge k))]; ring
    · intro t
      show ov d (S 0) t - (if t.val < (0 : Fin (n + 1)).val then d t else 0) =
        if t.val = 0 then a else 0
      rw [hS0]
      simp only [Fin.val_zero, Nat.not_lt_zero, ↓reduceIte, sub_zero]
      split_ifs with ht
      · exact ov_a_zero d a ha haf t ht
      · exact ov_a_pos hn d hd a haf t ht
    · intro i t hit
      show ov d (S i.castSucc) t - (if t.val < i.castSucc.val then d t else 0) +
          (ov d (S i.succ) t - ov d (S i.castSucc) t) =
          (if i = t then d t else 0) +
            (ov d (S i.succ) t - (if t.val < i.succ.val then d t else 0))
      have hit' : i.val ≤ t.val := Fin.le_def.1 hit
      simp only [Fin.val_castSucc, Fin.val_succ]
      rw [if_neg (show ¬ (t.val < i.val) by omega)]
      by_cases hieq : i = t
      · have hv : i.val = t.val := congrArg Fin.val hieq
        rw [if_pos hieq, if_pos (show t.val < i.val + 1 by omega)]; ring
      · have hv : i.val ≠ t.val := fun h => hieq (Fin.ext h)
        rw [if_neg hieq, if_neg (show ¬ (t.val < i.val + 1) by omega)]; ring
    · intro i t hit
      show ov d (S i.succ) t - ov d (S i.castSucc) t ≤
        (d t - (if t.val = 0 then a else 0)) * z.2.2 i
      rcases (hi i).2.1 with hy | hy
      · have hx : z.1 i = 0 := by
          have := (hi i).2.2.2
          rw [hy, mul_zero] at this
          linarith [(hi i).1]
        rw [hSsucc, hx, add_zero, hy, sub_self, mul_zero]
      · rw [hy, mul_one]
        split_ifs with ht
        · have hi0 : i.castSucc = 0 := Fin.ext (by
            simp only [Fin.val_castSucc, Fin.val_zero]
            have := Fin.le_def.1 hit
            omega)
          rw [hi0, hS0, ov_a_zero d a ha haf t ht]
          linarith [ov_le d hd (S i.succ) t]
        · linarith [ov_le d hd (S i.succ) t, ov_nonneg d hd (S i.castSucc) t]
  · show z = ((fun i => ∑ t, (ov d (S i.succ) t - ov d (S i.castSucc) t)),
      (fun k => ∑ t, (ov d (S k) t - (if t.val < k.val then d t else 0))), z.2.2)
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · funext i
      show z.1 i = ∑ t, (ov d (S i.succ) t - ov d (S i.castSucc) t)
      rw [Finset.sum_sub_distrib, ov_sum d _ (hSnn _) (hSle _), ov_sum d _ (hSnn _) (hSle _),
        hSsucc]
      ring
    · funext k
      show z.2.1 k = ∑ t, (ov d (S k) t - (if t.val < k.val then d t else 0))
      rw [Finset.sum_sub_distrib, ov_sum d _ (hSnn _) (hSle _)]
      show z.2.1 k = S k - Dc d k
      simp only [hSdef]
      ring

/-! ## Parent glue, part A: convexity of proj Q, conv X ⊆ proj Q, X compact -/

lemma Q_convex (n : ℕ) (d : Fin n → ℝ) (a : ℝ) :
    Convex ℝ {z | ∃ w v y, Qp n d a w v y ∧ z = proj w v y} := by
  rintro z1 ⟨w1, v1, y1, hQ1, rfl⟩ z2 ⟨w2, v2, y2, hQ2, rfl⟩ α β hα hβ hαβ
  obtain ⟨hw1, hv1, hy1, hwl1, hvl1, hv01, hbal1, hcap1⟩ := hQ1
  obtain ⟨hw2, hv2, hy2, hwl2, hvl2, hv02, hbal2, hcap2⟩ := hQ2
  refine ⟨α • w1 + β • w2, α • v1 + β • v2, α • y1 + β • y2, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hw1 i t, hw2 i t]
    · intro k t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hv1 k t, hv2 k t]
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      constructor <;> nlinarith [hy1 i, hy2 i]
    · intro i t h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hwl1 i t h, hwl2 i t h]
      ring
    · intro k t h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hvl1 k t h, hvl2 k t h]
      ring
    · intro t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv01 t, hv02 t]
      rw [← add_mul, hαβ, one_mul]
    · intro i t h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have e1 := hbal1 i t h
      have e2 := hbal2 i t h
      linear_combination α * e1 + β * e2 + (if i = t then d t else 0) * hαβ
    · intro i t h
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hcap1 i t h, hcap2 i t h, mul_le_mul_of_nonneg_left (hcap1 i t h) hα,
        mul_le_mul_of_nonneg_left (hcap2 i t h) hβ]
  · simp only [proj]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, Finset.mul_sum]
    · funext k
      simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
    · simp only [Prod.snd_add, Prod.smul_snd]

theorem hullX_sub_projQ (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t)
    (a : ℝ) (ha : 0 ≤ a) (haf : ∀ t : Fin n, t.val = 0 → a ≤ d t) :
    convexHull ℝ (Xs n d a) ⊆ {z | ∃ w v y, Qp n d a w v y ∧ z = proj w v y} :=
  convexHull_min (fun z hz => C1_holds n hn d hd a ha haf z hz) (Q_convex n d a)

lemma X_closed (n : ℕ) (d : Fin n → ℝ) (a : ℝ) : IsClosed (Xs n d a) := by
  unfold Xs
  simp only [Set.ofPred_and, Set.ofPred_forall, Set.ofPred_or]
  refine (isClosed_eq (by fun_prop) (by fun_prop)).inter
    ((isClosed_eq (by fun_prop) (by fun_prop)).inter
    ((isClosed_iInter fun k => isClosed_le (by fun_prop) (by fun_prop)).inter
    (isClosed_iInter fun i => (isClosed_le (by fun_prop) (by fun_prop)).inter
      (((isClosed_eq (by fun_prop) (by fun_prop)).union
        (isClosed_eq (by fun_prop) (by fun_prop))).inter
      ((isClosed_eq (by fun_prop) (by fun_prop)).inter
        (isClosed_le (by fun_prop) (by fun_prop)))))))

lemma s_le_total (n : ℕ) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (a : ℝ) (z)
    (hz : z ∈ Xs n d a) (k : Fin (n + 1)) : z.2.1 k ≤ Dc d (Fin.last n) := by
  obtain ⟨hs0, hsl, hsnn, hi⟩ := hz
  have hmono : Monotone (fun k => z.2.1 k + Dc d k) :=
    Fin.monotone_iff_le_succ.2 (fun i => by
      rw [Dc_succ]; linarith [(hi i).2.2.1, (hi i).1])
  have := hmono (Fin.le_last k)
  simp only [hsl] at this
  linarith [Dc_nonneg d hd k]

lemma X_compact (n : ℕ) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (a : ℝ) :
    IsCompact (Xs n d a) := by
  refine Metric.isCompact_of_isClosed_isBounded (X_closed n d a) ?_
  rw [isBounded_iff_forall_norm_le]
  have hT : 0 ≤ Dc d (Fin.last n) := Dc_nonneg d hd _
  have hsum : 0 ≤ ∑ t, d t := Finset.sum_nonneg (fun t _ => hd t)
  refine ⟨Dc d (Fin.last n) + ∑ t, d t + 1, fun z hz => ?_⟩
  have hR : 0 ≤ Dc d (Fin.last n) + ∑ t, d t + 1 := by linarith
  obtain ⟨hs0, hsl, hsnn, hi⟩ := hz
  have hz' : z ∈ Xs n d a := ⟨hs0, hsl, hsnn, hi⟩
  rw [norm_prod_le_iff, norm_prod_le_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [pi_norm_le_iff_of_nonneg hR]
    intro i
    rw [Real.norm_eq_abs, abs_le]
    have h1 := (hi i).2.2.2
    have h2 : ∑ t ∈ Finset.univ.filter (fun t => i ≤ t), d t ≤ ∑ t, d t :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun t _ _ => hd t)
    have h3 : 0 ≤ ∑ t ∈ Finset.univ.filter (fun t => i ≤ t), d t :=
      Finset.sum_nonneg (fun t _ => hd t)
    constructor
    · linarith [(hi i).1]
    · rcases (hi i).2.1 with hy | hy <;> rw [hy] at h1 <;> nlinarith
  · rw [pi_norm_le_iff_of_nonneg hR]
    intro k
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · linarith [hsnn k]
    · linarith [s_le_total n d hd a z hz' k]
  · rw [pi_norm_le_iff_of_nonneg hR]
    intro i
    rw [Real.norm_eq_abs, abs_le]
    rcases (hi i).2.1 with hy | hy <;> rw [hy] <;> constructor <;> linarith

/-! ## Parent glue, part B: compact hull, functional representation, separation -/

lemma isCompact_convexHull_of_compact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {X : Set E} (hX : IsCompact X) : IsCompact (convexHull ℝ X) := by
  classical
  let F : (m : ℕ) → (Fin m → ℝ) × (Fin m → E) → E := fun m p => ∑ j, p.1 j • p.2 j
  have hFc : ∀ m, Continuous (F m) := fun m =>
    continuous_finsetSum _ (fun j _ =>
      ((continuous_apply j).comp continuous_fst).smul ((continuous_apply j).comp continuous_snd))
  have hK : convexHull ℝ X = ⋃ m : Fin (Module.finrank ℝ E + 2),
      F m '' (stdSimplex ℝ (Fin m) ×ˢ Set.univ.pi (fun _ => X)) := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [convexHull_eq_union] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨t, htX, hai, hxt⟩ := hx
      have hcard : t.card ≤ Module.finrank ℝ E + 1 := by
        have h1 := hai.card_le_finrank_succ
        have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : t → E)))
        simp only [Fintype.card_coe] at h1
        omega
      rw [Finset.mem_convexHull] at hxt
      obtain ⟨w, hw0, hw1, hwx⟩ := hxt
      rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hwx
      let g : Fin t.card ≃ t := t.equivFin.symm
      refine Set.mem_iUnion.2 ⟨⟨t.card, by omega⟩, ⟨(fun j => w (g j), fun j => (g j : E)),
        ⟨⟨fun j => hw0 _ (g j).2, ?_⟩, ?_⟩, ?_⟩⟩
      · exact (Equiv.sum_comp g (fun e : t => w e)).trans ((Finset.sum_coe_sort t w).trans hw1)
      · intro j _; exact htX (g j).2
      · exact (Equiv.sum_comp g (fun e : t => w e • (e : E))).trans
          ((Finset.sum_coe_sort t (fun e => w e • id e)).trans hwx)
    · refine Set.iUnion_subset (fun m => ?_)
      rintro _ ⟨p, ⟨⟨h0, h1⟩, hpX⟩, rfl⟩
      exact (convex_convexHull ℝ X).sum_mem (fun j _ => h0 j) h1
        (fun j _ => subset_convexHull ℝ X (hpX j (Set.mem_univ _)))
  rw [hK]
  refine isCompact_iUnion (fun m => IsCompact.image ?_ (hFc m))
  refine IsCompact.prod ?_ (isCompact_univ_pi (fun _ => hX))
  first
    | exact isCompact_stdSimplex
    | exact isCompact_stdSimplex ℝ (Fin m)
    | exact isCompact_stdSimplex (Fin m)

lemma isum_succ {n : ℕ} (g : Fin n → ℝ) (t : Fin n) :
    (∑ u : Fin n, if u.val < t.val + 1 then g u else 0) =
      (∑ u : Fin n, if u.val < t.val then g u else 0) + g t := by
  have hgi : g t = ∑ j, if j = t then g j else 0 := by simp
  rw [hgi, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hji : j = t
  · subst hji; simp
  · have : j.val ≠ t.val := fun h => hji (Fin.ext h)
    simp only [if_neg hji, add_zero]
    by_cases hlt : j.val < t.val
    · rw [if_pos hlt, if_pos (show j.val < t.val + 1 by omega)]
    · rw [if_neg hlt, if_neg (show ¬ (j.val < t.val + 1) by omega)]

lemma s_closed_form {n : ℕ} (d : Fin n → ℝ) (a : ℝ)
    (z : (Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)) (hs0 : z.2.1 0 = a)
    (hbal : ∀ i : Fin n, z.2.1 i.castSucc + z.1 i = d i + z.2.1 i.succ) (k : Fin (n + 1)) :
    z.2.1 k = a - Dc d k + ∑ j : Fin n, if j.val < k.val then z.1 j else 0 := by
  induction k using Fin.induction with
  | zero => simp [hs0, Dc_zero]
  | succ i ih =>
    rw [Dc_succ]
    have h := isum_succ z.1 i
    simp only [Fin.val_succ, Fin.val_castSucc] at ih ⊢
    rw [h]
    linarith [hbal i]

noncomputable def cX {n : ℕ} (f : StrongDual ℝ ((Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)))
    (i : Fin n) : ℝ := f ((Pi.single i 1 : Fin n → ℝ), (0 : Fin (n + 1) → ℝ), (0 : Fin n → ℝ))
noncomputable def cS {n : ℕ} (f : StrongDual ℝ ((Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)))
    (k : Fin (n + 1)) : ℝ :=
  f ((0 : Fin n → ℝ), (Pi.single k 1 : Fin (n + 1) → ℝ), (0 : Fin n → ℝ))
noncomputable def cY {n : ℕ} (f : StrongDual ℝ ((Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)))
    (i : Fin n) : ℝ := f ((0 : Fin n → ℝ), (0 : Fin (n + 1) → ℝ), (Pi.single i 1 : Fin n → ℝ))

lemma f_expand {n : ℕ} (f : StrongDual ℝ ((Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)))
    (z : (Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)) :
    f z = ∑ i, z.1 i * cX f i + ∑ k, z.2.1 k * cS f k + ∑ i, z.2.2 i * cY f i := by
  have hz : z = ∑ i, z.1 i • ((Pi.single i 1 : Fin n → ℝ), (0 : Fin (n + 1) → ℝ), (0 : Fin n → ℝ))
      + ∑ k, z.2.1 k • ((0 : Fin n → ℝ), (Pi.single k 1 : Fin (n + 1) → ℝ), (0 : Fin n → ℝ))
      + ∑ i, z.2.2 i • ((0 : Fin n → ℝ), (0 : Fin (n + 1) → ℝ), (Pi.single i 1 : Fin n → ℝ)) := by
    ext j <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz]
  simp only [map_add, map_sum, map_smul, smul_eq_mul, cX, cS, cY]

lemma functional_rep (n : ℕ) (d : Fin n → ℝ) (a : ℝ)
    (f : StrongDual ℝ ((Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ))) :
    ∃ (φ γ : Fin n → ℝ) (C : ℝ), ∀ z : (Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ),
      z.2.1 0 = a → (∀ i : Fin n, z.2.1 i.castSucc + z.1 i = d i + z.2.1 i.succ) →
      f z = C + ∑ i, (φ i * z.1 i + γ i * z.2.2 i) := by
  refine ⟨fun j => cX f j + ∑ k, (if j.val < k.val then cS f k else 0), cY f,
    ∑ k, (a - Dc d k) * cS f k, fun z hs0 hbal => ?_⟩
  rw [f_expand f z]
  have hS : ∑ k, z.2.1 k * cS f k = ∑ k, (a - Dc d k) * cS f k +
      ∑ j, z.1 j * ∑ k, (if j.val < k.val then cS f k else 0) := by
    rw [Finset.sum_congr rfl (fun k _ => by rw [s_closed_form d a z hs0 hbal k])]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, ite_mul,
      zero_mul, mul_ite, mul_zero]
    congr 1
    exact Finset.sum_comm
  rw [hS]
  have e : ∑ i, ((cX f i + ∑ k, (if i.val < k.val then cS f k else 0)) * z.1 i +
      cY f i * z.2.2 i) = ∑ i, z.1 i * cX f i +
        ∑ j, z.1 j * ∑ k, (if j.val < k.val then cS f k else 0) + ∑ i, z.2.2 i * cY f i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  beta_reduce
  rw [e]
  ring

lemma projQ_bal (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ) (a : ℝ) (w : Fin n → Fin n → ℝ)
    (v : Fin (n + 1) → Fin n → ℝ) (y : Fin n → ℝ) (hQ : Qp n d a w v y) :
    (proj w v y).2.1 0 = a ∧ ∀ i : Fin n,
      (proj w v y).2.1 i.castSucc + (proj w v y).1 i = d i + (proj w v y).2.1 i.succ := by
  have hQ' := hQ
  obtain ⟨hw, hv, hy, hwl, hvl, hv0, hbal, hcap⟩ := hQ
  refine ⟨?_, ?_⟩
  · show ∑ t, v 0 t = a
    rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
    · rw [hv0]; simp
    · intro b _ hb
      rw [hv0, if_neg]
      intro h0; exact hb (Fin.ext h0)
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i
    show ∑ t, v i.castSucc t + ∑ t, w i t = d i + ∑ t, v i.succ t
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun t _ => bal_all n d a w v y hQ' i t),
      Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp

theorem projQ_sub_hullX (H2 : C2_round) (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ)
    (hd : ∀ t, 0 ≤ d t) (a : ℝ) (ha : 0 ≤ a) (haf : ∀ t : Fin n, t.val = 0 → a ≤ d t) :
    {z | ∃ w v y, Qp n d a w v y ∧ z = proj w v y} ⊆ convexHull ℝ (Xs n d a) := by
  rintro _ ⟨w, v, y, hQ, rfl⟩
  by_contra hnot
  obtain ⟨f, u, hfX, hfz⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ (Xs n d a))
    (isCompact_convexHull_of_compact (X_compact n d hd a)).isClosed hnot
  obtain ⟨φ, γ, C, hrep⟩ := functional_rep n d a f
  obtain ⟨z', hz'X, hle⟩ := H2 n hn d hd a ha haf (fun i => -φ i) (fun i => -γ i) w v y hQ
  have h1 := hfX z' (subset_convexHull ℝ _ hz'X)
  rw [hrep z' hz'X.1 (fun i => (hz'X.2.2.2 i).2.2.1)] at h1
  obtain ⟨hb0, hbb⟩ := projQ_bal n hn d a w v y hQ
  rw [hrep _ hb0 hbb] at hfz
  have e1 : ∑ i, (-φ i * z'.1 i + -γ i * z'.2.2 i) =
      -∑ i, (φ i * z'.1 i + γ i * z'.2.2 i) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have e2 : ∑ i, (-φ i * (proj w v y).1 i + -γ i * y i) =
      -∑ i, (φ i * (proj w v y).1 i + γ i * (proj w v y).2.2 i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun i _ => by simp only [proj]; ring)
  beta_reduce at hle
  rw [e1, e2] at hle
  linarith

/-! ## Parent glue, part C: the cost and the assembled statement -/

noncomputable def costF {n : ℕ} (p h q : ℝ)
    (z : (Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)) : ℝ :=
  (∑ i, (p * z.1 i + q * z.2.2 i)) + (∑ i : Fin n, h * z.2.1 i.succ)

lemma costF_cont {n : ℕ} (p h q : ℝ) : Continuous (costF (n := n) p h q) := by
  unfold costF
  fun_prop

lemma costF_superlevel_convex {n : ℕ} (p h q c : ℝ) :
    Convex ℝ {z : (Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ) | c ≤ costF p h q z} := by
  intro z1 h1 z2 h2 α β hα hβ hαβ
  have key : costF p h q (α • z1 + β • z2) = α * costF p h q z1 + β * costF p h q z2 := by
    simp only [costF, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have e1 : ∑ i, (p * (α * z1.1 i + β * z2.1 i) + q * (α * z1.2.2 i + β * z2.2.2 i)) =
        ∑ i, (α * (p * z1.1 i + q * z1.2.2 i) + β * (p * z2.1 i + q * z2.2.2 i)) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    have e2 : ∑ i : Fin n, h * (α * z1.2.1 i.succ + β * z2.2.1 i.succ) =
        ∑ i : Fin n, (α * (h * z1.2.1 i.succ) + β * (h * z2.2.1 i.succ)) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [e1, e2]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  show c ≤ costF p h q (α • z1 + β • z2)
  rw [key]
  have h1' : c ≤ costF p h q z1 := h1
  have h2' : c ≤ costF p h q z2 := h2
  have hc : c = α * c + β * c := by rw [← add_mul, hαβ, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1' hα, mul_le_mul_of_nonneg_left h2' hβ]

lemma X_nonempty (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t) (a : ℝ)
    (ha : 0 ≤ a) (haf : ∀ t : Fin n, t.val = 0 → a ≤ d t) : (Xs n d a).Nonempty := by
  refine ⟨(fun i => d i - (if i.val = 0 then a else 0), fun k => if k.val = 0 then a else 0,
    fun _ => 1), ?_, ?_, ?_, ?_⟩
  · show (if (0 : Fin (n + 1)).val = 0 then a else 0) = a
    simp
  · show (if (Fin.last n).val = 0 then a else 0) = 0
    rw [Fin.val_last, if_neg (show ¬ (n = 0) by omega)]
  · intro k
    show 0 ≤ (if k.val = 0 then a else 0)
    split_ifs <;> linarith
  · intro i
    refine ⟨?_, Or.inr rfl, ?_, ?_⟩
    · show 0 ≤ d i - (if i.val = 0 then a else 0)
      split_ifs with h0
      · linarith [haf i h0]
      · linarith [hd i]
    · show (if i.castSucc.val = 0 then a else 0) + (d i - (if i.val = 0 then a else 0)) =
        d i + (if i.succ.val = 0 then a else 0)
      simp only [Fin.val_castSucc, Fin.val_succ]
      rw [if_neg (show ¬ (i.val + 1 = 0) by omega)]
      split_ifs <;> ring
    · show d i - (if i.val = 0 then a else 0) ≤
        (∑ t ∈ Finset.univ.filter (fun t => i ≤ t), d t) * 1
      have hle : d i ≤ ∑ t ∈ Finset.univ.filter (fun t => i ≤ t), d t :=
        Finset.single_le_sum (f := d) (fun t _ => hd t)
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl⟩)
      split_ifs <;> linarith

theorem main_of (H2 : C2_round) (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t)
    (a : ℝ) (ha : 0 ≤ a) (haf : ∀ t : Fin n, t.val = 0 → a ≤ d t) (p h q : ℝ) :
    {z | ∃ w v y, Qp n d a w v y ∧ z = proj w v y} = convexHull ℝ (Xs n d a) ∧
      ∃ w v y, Qp n d a w v y ∧ (∀ i, y i = 0 ∨ y i = 1) ∧
        (∀ w' v' y', Qp n d a w' v' y' →
          costF p h q (proj w v y) ≤ costF p h q (proj w' v' y')) ∧
        proj w v y ∈ Xs n d a ∧ (∀ z ∈ Xs n d a, costF p h q (proj w v y) ≤ costF p h q z) := by
  have hEq := Set.Subset.antisymm (projQ_sub_hullX H2 n hn d hd a ha haf)
    (hullX_sub_projQ n hn d hd a ha haf)
  refine ⟨hEq, ?_⟩
  obtain ⟨zs, hzsX, hmin⟩ := (X_compact n d hd a).exists_isMinOn
    (X_nonempty n hn d hd a ha haf) (costF_cont p h q).continuousOn
  have hmin' : ∀ z ∈ Xs n d a, costF p h q zs ≤ costF p h q z := isMinOn_iff.1 hmin
  obtain ⟨w, v, y, hQ, hzs⟩ := C1_holds n hn d hd a ha haf zs hzsX
  have hy : y = zs.2.2 := by rw [hzs]; rfl
  refine ⟨w, v, y, hQ, fun i => by rw [hy]; exact (hzsX.2.2.2 i).2.1, ?_,
    by rw [← hzs]; exact hzsX, fun z hz => by rw [← hzs]; exact hmin' z hz⟩
  intro w' v' y' hQ'
  have hmem : proj w' v' y' ∈ convexHull ℝ (Xs n d a) := by
    rw [← hEq]; exact ⟨w', v', y', hQ', rfl⟩
  have hsub : convexHull ℝ (Xs n d a) ⊆ {z | costF p h q zs ≤ costF p h q z} :=
    convexHull_min (fun z hz => hmin' z hz) (costF_superlevel_convex p h q _)
  rw [← hzs]
  exact hsub hmem

section C2a

variable {n : ℕ}

/-- expectation over a finite weighted list of scenarios -/
noncomputable def Ex (P : List (ℝ × Finset (Fin n))) (h : Finset (Fin n) → ℝ) : ℝ :=
  (P.map (fun p => p.1 * h p.2)).sum

lemma Ex_cons (p : ℝ × Finset (Fin n)) (P : List (ℝ × Finset (Fin n)))
    (h : Finset (Fin n) → ℝ) : Ex (p :: P) h = p.1 * h p.2 + Ex P h := by
  simp [Ex]

lemma Ex_nil (h : Finset (Fin n) → ℝ) : Ex ([] : List (ℝ × Finset (Fin n))) h = 0 := by
  simp [Ex]

lemma Ex_zero (P : List (ℝ × Finset (Fin n))) : Ex P (fun _ => (0:ℝ)) = 0 := by
  induction P with
  | nil => simp [Ex_nil]
  | cons p P ih => rw [Ex_cons, ih]; ring

lemma Ex_add (P : List (ℝ × Finset (Fin n))) (h1 h2 : Finset (Fin n) → ℝ) :
    Ex P (fun S => h1 S + h2 S) = Ex P h1 + Ex P h2 := by
  induction P with
  | nil => simp [Ex_nil]
  | cons p P ih => rw [Ex_cons, Ex_cons, Ex_cons, ih]; ring

lemma Ex_smul (P : List (ℝ × Finset (Fin n))) (r : ℝ) (h : Finset (Fin n) → ℝ) :
    Ex P (fun S => r * h S) = r * Ex P h := by
  induction P with
  | nil => simp [Ex_nil]
  | cons p P ih => rw [Ex_cons, Ex_cons, ih]; ring

lemma Ex_sub (P : List (ℝ × Finset (Fin n))) (h1 h2 : Finset (Fin n) → ℝ) :
    Ex P (fun S => h1 S - h2 S) = Ex P h1 - Ex P h2 := by
  induction P with
  | nil => simp [Ex_nil]
  | cons p P ih => rw [Ex_cons, Ex_cons, Ex_cons, ih]; ring

lemma Ex_congr (P : List (ℝ × Finset (Fin n))) (h1 h2 : Finset (Fin n) → ℝ)
    (H : ∀ p ∈ P, h1 p.2 = h2 p.2) : Ex P h1 = Ex P h2 := by
  induction P with
  | nil => simp [Ex_nil]
  | cons p P ih =>
    rw [Ex_cons, Ex_cons, H p (by simp), ih (fun q hq => H q (by simp [hq]))]

lemma Ex_congr' (P : List (ℝ × Finset (Fin n))) (h1 h2 : Finset (Fin n) → ℝ)
    (H : ∀ S, h1 S = h2 S) : Ex P h1 = Ex P h2 := Ex_congr P h1 h2 (fun p _ => H p.2)

lemma Ex_congr_sub (P : List (ℝ × Finset (Fin n))) (s : Finset (Fin n))
    (hsup : ∀ p ∈ P, p.2 ⊆ s) (h1 h2 : Finset (Fin n) → ℝ)
    (H : ∀ S, S ⊆ s → h1 S = h2 S) : Ex P h1 = Ex P h2 :=
  Ex_congr P h1 h2 (fun p hp => H p.2 (hsup p hp))

lemma Ex_mono (P : List (ℝ × Finset (Fin n))) (hw : ∀ p ∈ P, 0 ≤ p.1)
    (h1 h2 : Finset (Fin n) → ℝ) (H : ∀ p ∈ P, h1 p.2 ≤ h2 p.2) : Ex P h1 ≤ Ex P h2 := by
  induction P with
  | nil => simp [Ex_nil]
  | cons p P ih =>
    rw [Ex_cons, Ex_cons]
    have h3 := mul_le_mul_of_nonneg_left (H p (by simp)) (hw p (by simp))
    have h4 := ih (fun q hq => hw q (by simp [hq])) (fun q hq => H q (by simp [hq]))
    linarith

lemma Ex_sum (P : List (ℝ × Finset (Fin n))) (I : Finset (Fin n))
    (h : Fin n → Finset (Fin n) → ℝ) :
    Ex P (fun S => ∑ i ∈ I, h i S) = ∑ i ∈ I, Ex P (h i) := by
  induction P with
  | nil => simp [Ex_nil]
  | cons p P ih =>
    rw [Ex_cons, ih]
    simp only [Ex_cons, Finset.sum_add_distrib, Finset.mul_sum]

lemma Ex_nonneg_of (P : List (ℝ × Finset (Fin n))) (hw : ∀ p ∈ P, 0 ≤ p.1)
    (k : Finset (Fin n) → ℝ) (hk : ∀ p ∈ P, 0 < p.1 → 0 < k p.2) : 0 ≤ Ex P k := by
  induction P with
  | nil => simp [Ex_nil]
  | cons p P ih =>
    rw [Ex_cons]
    have h1 : 0 ≤ p.1 * k p.2 := by
      rcases (hw p (by simp)).lt_or_eq with h | h
      · exact (mul_pos h (hk p (by simp) h)).le
      · rw [← h]; simp
    have h2 := ih (fun q hq => hw q (by simp [hq])) (fun q hq => hk q (by simp [hq]))
    linarith

lemma Ex_pos_of (P : List (ℝ × Finset (Fin n))) (hw : ∀ p ∈ P, 0 ≤ p.1)
    (k : Finset (Fin n) → ℝ) (hk : ∀ p ∈ P, 0 < p.1 → 0 < k p.2)
    (h1 : 0 < Ex P (fun _ => 1)) : 0 < Ex P k := by
  induction P with
  | nil => simp [Ex_nil] at h1
  | cons p P ih =>
    rw [Ex_cons] at h1 ⊢
    have hw' : ∀ q ∈ P, 0 ≤ q.1 := fun q hq => hw q (by simp [hq])
    have hk' : ∀ q ∈ P, 0 < q.1 → 0 < k q.2 := fun q hq => hk q (by simp [hq])
    rcases (hw p (by simp)).lt_or_eq with h | h
    · have := mul_pos h (hk p (by simp) h)
      have := Ex_nonneg_of P hw' k hk'
      linarith
    · rw [← h] at h1 ⊢
      simp only [zero_mul, zero_add] at h1 ⊢
      exact ih hw' hk' h1

lemma Ex_exists_le (P : List (ℝ × Finset (Fin n))) (hw : ∀ p ∈ P, 0 ≤ p.1)
    (h : Finset (Fin n) → ℝ) (c : ℝ) (h1 : Ex P (fun _ => 1) = 1) (hc : Ex P h ≤ c) :
    ∃ p ∈ P, 0 < p.1 ∧ h p.2 ≤ c := by
  by_contra hne
  push_neg at hne
  have hpos := Ex_pos_of P hw (fun S => h S - c * 1) (fun p hp h0 => by
    have := hne p hp h0; simp only [mul_one]; linarith) (by rw [h1]; norm_num)
  rw [Ex_sub, Ex_smul, h1] at hpos
  linarith

lemma Ex_zero_of (P : List (ℝ × Finset (Fin n))) (hw : ∀ p ∈ P, 0 ≤ p.1)
    (k : Finset (Fin n) → ℝ) (hk : ∀ S, 0 ≤ k S) (hE : Ex P k ≤ 0) :
    ∀ p ∈ P, 0 < p.1 → k p.2 = 0 := by
  induction P with
  | nil => intro p hp; simp at hp
  | cons q P ih =>
    intro p hp hp0
    rw [Ex_cons] at hE
    have hw' : ∀ r ∈ P, 0 ≤ r.1 := fun r hr => hw r (by simp [hr])
    have hP0 : 0 ≤ Ex P k := by
      have := Ex_mono P hw' (fun _ => 0) k (fun r _ => hk r.2)
      rw [Ex_zero] at this; exact this
    have hq0 : 0 ≤ q.1 * k q.2 := mul_nonneg (hw q (by simp)) (hk q.2)
    rcases List.mem_cons.1 hp with rfl | hp'
    · have : p.1 * k p.2 ≤ 0 := by linarith
      have h2 : k p.2 ≤ 0 := by
        by_contra hcon; push_neg at hcon; linarith [mul_pos hp0 hcon]
      exact le_antisymm h2 (hk _)
    · exact ih hw' (by linarith) p hp' hp0

/-- indicator that every element of `S` has index at least `c` -/
noncomputable def ind (c : ℕ) (S : Finset (Fin n)) : ℝ :=
  if ∀ j ∈ S, c ≤ j.val then 1 else 0

lemma ind_nonneg (c : ℕ) (S : Finset (Fin n)) : 0 ≤ ind c S := by
  unfold ind; split_ifs <;> norm_num

/-- cheapest open facility available to client `t`, capped at `ψ` -/
noncomputable def V (φ : Fin n → ℝ) (S : Finset (Fin n)) (t : Fin n) (ψ : ℝ) : ℝ :=
  (S.filter (fun i => i ≤ t)).fold min ψ φ

lemma V_of_G (φ : Fin n → ℝ) (S : Finset (Fin n)) (t : Fin n) (ψ : ℝ)
    (hG : ∀ j ∈ S, t.val + 1 ≤ j.val) : V φ S t ψ = ψ := by
  unfold V
  have : S.filter (fun i => i ≤ t) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro j hj hjt
    have := hG j hj
    have : j.val ≤ t.val := hjt
    omega
  rw [this, Finset.fold_empty]

lemma V_le (φ : Fin n → ℝ) (S : Finset (Fin n)) (t : Fin n) (ψ : ℝ) : V φ S t ψ ≤ ψ := by
  unfold V; rw [Finset.fold_min_le]; left; exact le_rfl

lemma V_of_notG (φ : Fin n → ℝ) (S : Finset (Fin n)) (t : Fin n) (ψ ψ0 : ℝ)
    (hS : ∀ i ∈ S, φ i ≤ ψ0) (hψ : ψ0 ≤ ψ) (hG : ¬ ∀ j ∈ S, t.val + 1 ≤ j.val) :
    V φ S t ψ = V φ S t ψ0 := by
  push_neg at hG
  obtain ⟨j, hjS, hjt⟩ := hG
  have hjf : j ∈ S.filter (fun i => i ≤ t) := by
    rw [Finset.mem_filter]; exact ⟨hjS, by show j.val ≤ t.val; omega⟩
  unfold V
  apply le_antisymm
  · rw [Finset.le_fold_min]
    refine ⟨?_, fun x hx => ?_⟩
    · rw [Finset.fold_min_le]; right; exact ⟨j, hjf, hS j hjS⟩
    · rw [Finset.fold_min_le]; right; exact ⟨x, hx, le_rfl⟩
  · rw [Finset.le_fold_min]
    refine ⟨?_, fun x hx => ?_⟩
    · rw [Finset.fold_min_le]; left; exact hψ
    · rw [Finset.fold_min_le]; right; exact ⟨x, hx, le_rfl⟩

lemma V_insert (φ : Fin n → ℝ) (S : Finset (Fin n)) (t : Fin n) (ψ : ℝ) (a : Fin n)
    (ha : a ∉ S) :
    V φ (insert a S) t ψ = if a ≤ t then min (φ a) (V φ S t ψ) else V φ S t ψ := by
  unfold V
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.fold_insert]
    rw [Finset.mem_filter]; exact fun h' => ha h'.1
  · rfl

/-- the per-scenario identity behind the coupling step -/
lemma scen (φ : Fin n → ℝ) (S : Finset (Fin n)) (t : Fin n) (ψ lam : ℝ) (a : Fin n)
    (ha : a ∉ S) (hS : ∀ i ∈ S, φ i ≤ φ a) (hψ : φ a ≤ ψ) :
    (1 - lam) * V φ S t ψ + lam * V φ (insert a S) t ψ =
      V φ S t (φ a) + (ψ - φ a) * ((1 - lam) * ind (t.val + 1) S +
        lam * ind (t.val + 1) (insert a S)) := by
  rw [V_insert φ S t ψ a ha]
  by_cases hG : ∀ j ∈ S, t.val + 1 ≤ j.val
  · have e1 := V_of_G φ S t ψ hG
    have e2 := V_of_G φ S t (φ a) hG
    have i1 : ind (t.val + 1) S = 1 := by unfold ind; rw [if_pos hG]
    split_ifs with hat
    · have i2 : ind (t.val + 1) (insert a S) = 0 := by
        unfold ind; rw [if_neg]; push_neg
        exact ⟨a, Finset.mem_insert_self a S, by have : a.val ≤ t.val := hat; omega⟩
      rw [e1, e2, i1, i2, min_eq_left hψ]; ring
    · have i2 : ind (t.val + 1) (insert a S) = 1 := by
        unfold ind; rw [if_pos]
        intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · push_neg at hat; exact hat
        · exact hG j hj
      rw [e1, e2, i1, i2]; ring
  · have e1 := V_of_notG φ S t ψ (φ a) hS hψ hG
    have i1 : ind (t.val + 1) S = 0 := by unfold ind; rw [if_neg hG]
    have hle : V φ S t (φ a) ≤ φ a := V_le φ S t (φ a)
    split_ifs with hat
    · have i2 : ind (t.val + 1) (insert a S) = 0 := by
        unfold ind; rw [if_neg]; push_neg
        exact ⟨a, Finset.mem_insert_self a S, by have : a.val ≤ t.val := hat; omega⟩
      rw [e1, i1, i2, min_eq_right hle]; ring
    · have i2 : ind (t.val + 1) (insert a S) = 0 := by
        unfold ind; rw [if_neg]; intro hall; exact hG (fun j hj => hall j (Finset.mem_insert_of_mem hj))
      rw [e1, i1, i2]; ring

/-- the coupling step: split every scenario, adding facility `a` with fraction `lam` -/
def stepL (a : Fin n) (lam : Finset (Fin n) → ℝ) :
    List (ℝ × Finset (Fin n)) → List (ℝ × Finset (Fin n))
  | [] => []
  | p :: P => (p.1 * (1 - lam p.2), p.2) :: (p.1 * lam p.2, insert a p.2) :: stepL a lam P

lemma Ex_stepL (a : Fin n) (lam : Finset (Fin n) → ℝ) (P : List (ℝ × Finset (Fin n)))
    (h : Finset (Fin n) → ℝ) :
    Ex (stepL a lam P) h = Ex P (fun S => (1 - lam S) * h S + lam S * h (insert a S)) := by
  induction P with
  | nil => simp [stepL, Ex_nil]
  | cons p P ih => simp only [stepL, Ex_cons, ih]; ring

lemma mem_stepL (a : Fin n) (lam : Finset (Fin n) → ℝ) (P : List (ℝ × Finset (Fin n)))
    (q : ℝ × Finset (Fin n)) (hq : q ∈ stepL a lam P) :
    ∃ p ∈ P, q = (p.1 * (1 - lam p.2), p.2) ∨ q = (p.1 * lam p.2, insert a p.2) := by
  induction P with
  | nil => simp [stepL] at hq
  | cons p P ih =>
    simp only [stepL, List.mem_cons] at hq
    rcases hq with h | h | h
    · exact ⟨p, by simp, Or.inl h⟩
    · exact ⟨p, by simp, Or.inr h⟩
    · obtain ⟨r, hr, hr'⟩ := ih h
      exact ⟨r, by simp [hr], hr'⟩

lemma ind_mono (c c' : ℕ) (hc : c ≤ c') (S : Finset (Fin n)) :
    ind c' S = 1 → ind c S = 1 := by
  unfold ind; intro h
  split_ifs at h with h'
  · rw [if_pos (fun j hj => le_trans hc (h' j hj))]
  · norm_num at h

lemma ind_zero_or_one (c : ℕ) (S : Finset (Fin n)) : ind c S = 0 ∨ ind c S = 1 := by
  unfold ind; split_ifs <;> simp

lemma waterfill (P : List (ℝ × Finset (Fin n))) (hw : ∀ p ∈ P, 0 ≤ p.1)
    (h1 : Ex P (fun _ => 1) = 1) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ∃ lam : Finset (Fin n) → ℝ, (∀ S, 0 ≤ lam S ∧ lam S ≤ 1) ∧ Ex P lam = y ∧
      ∀ c ≤ n, (∀ S, ind c S = 1 → lam S = 1) ∨ (∀ S, lam S ≠ 0 → ind c S = 1) := by
  set F : ℕ → ℝ := fun c => Ex P (ind c) with hF
  have Fnn : ∀ c, 0 ≤ F c := fun c => by
    have := Ex_mono P hw (fun _ => 0) (ind c) (fun p _ => ind_nonneg c p.2)
    rw [Ex_zero] at this; exact this
  have F0 : F 0 = 1 := by
    simp only [hF]; rw [← h1]; apply Ex_congr; intro p _; unfold ind; rw [if_pos]; intro j _; omega
  by_cases hyn : y ≤ F n
  · by_cases hFn : F n = 0
    · refine ⟨fun _ => 0, fun S => by simp, ?_, fun c _ => Or.inr (fun S h => absurd rfl h)⟩
      have hy : y = 0 := le_antisymm (hFn ▸ hyn) hy0
      rw [Ex_zero, hy]
    · have hFpos : 0 < F n := lt_of_le_of_ne (Fnn n) (Ne.symm hFn)
      refine ⟨fun S => y / F n * ind n S, fun S => ?_, ?_, fun c hc => Or.inr ?_⟩
      · have hq0 : 0 ≤ y / F n := div_nonneg hy0 hFpos.le
        have hq1 : y / F n ≤ 1 := (div_le_one hFpos).2 hyn
        dsimp only
        rcases ind_zero_or_one n S with h | h <;> rw [h] <;> constructor <;> nlinarith
      · rw [Ex_smul]; exact div_mul_cancel₀ y hFn
      · intro S hS
        dsimp only at hS
        rcases ind_zero_or_one n S with h | h
        · rw [h, mul_zero] at hS; exact absurd rfl hS
        · exact ind_mono c n hc S h
  · push_neg at hyn
    have hex : ∃ k, F k < y := ⟨n, hyn⟩
    have hk : F (Nat.find hex) < y := Nat.find_spec hex
    have hkn : Nat.find hex ≤ n := Nat.find_min' hex hyn
    have hk0 : Nat.find hex ≠ 0 := by
      intro h; rw [h, F0] at hk; linarith
    obtain ⟨c, hc⟩ : ∃ c, Nat.find hex = c + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hFc : y ≤ F c := by
      have := Nat.find_min hex (show c < Nat.find hex by omega); push_neg at this; exact this
    rw [hc] at hk hkn
    have hden : 0 < F c - F (c + 1) := by linarith
    set θ := (y - F (c + 1)) / (F c - F (c + 1)) with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hden.le
    have hθ1 : θ ≤ 1 := (div_le_one hden).2 (by linarith)
    refine ⟨fun S => ind (c + 1) S + θ * (ind c S - ind (c + 1) S), fun S => ?_, ?_,
      fun c' hc' => ?_⟩
    · dsimp only
      rcases ind_zero_or_one (c + 1) S with h | h
      · rcases ind_zero_or_one c S with h' | h' <;> rw [h, h'] <;> constructor <;> linarith
      · rw [h, ind_mono c (c + 1) (by omega) S h]; constructor <;> linarith
    · rw [Ex_add, Ex_smul, Ex_sub]
      show F (c + 1) + θ * (F c - F (c + 1)) = y
      rw [hθ]; field_simp; ring
    · by_cases hcc : c + 1 ≤ c'
      · left; intro S hS
        dsimp only
        have h2 := ind_mono (c + 1) c' hcc S hS
        rw [h2, ind_mono c (c + 1) (by omega) S h2]; ring
      · right; intro S hS
        dsimp only at hS
        rcases ind_zero_or_one c S with h | h
        · have h2 : ind (c + 1) S = 0 := by
            rcases ind_zero_or_one (c + 1) S with h3 | h3
            · exact h3
            · rw [ind_mono c (c + 1) (by omega) S h3] at h; norm_num at h
          rw [h, h2] at hS; simp at hS
        · exact ind_mono c' c (by omega) S h

lemma build (D : Fin n → ℝ) (f : Fin n → Fin n → ℝ) (y : Fin n → ℝ)
    (hf0 : ∀ i t, 0 ≤ f i t) (hfl : ∀ i t, t < i → f i t = 0) (hfs : ∀ t, ∑ i, f i t = D t)
    (hcap : ∀ i t, f i t ≤ D t * y i) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (φ γ : Fin n → ℝ)
    (s : Finset (Fin n)) :
    ∃ P : List (ℝ × Finset (Fin n)), (∀ p ∈ P, 0 ≤ p.1) ∧ Ex P (fun _ => 1) = 1 ∧
      (∀ p ∈ P, p.2 ⊆ s) ∧
      Ex P (fun S => ∑ i ∈ S, γ i) = ∑ i ∈ s, γ i * y i ∧
      (∀ t : Fin n, D t * Ex P (ind (t.val + 1)) ≤ D t - ∑ i ∈ s, f i t) ∧
      (∀ t : Fin n, ∀ ψ : ℝ, (∀ i ∈ s, φ i ≤ ψ) →
        Ex P (fun S => D t * V φ S t ψ) ≤
          ∑ i ∈ s, φ i * f i t + ψ * (D t - ∑ i ∈ s, f i t)) := by
  induction s using Finset.induction_on_max_value φ with
  | empty =>
    refine ⟨[(1, ∅)], by simp, by simp [Ex], by simp, by simp [Ex], fun t => ?_,
      fun t ψ _ => ?_⟩
    · simp [Ex, ind]
    · simp [Ex, V]; linarith
  | insert a s has hmax ih =>
    obtain ⟨P, hw, h1, hsup, hγ, hemp, hcost⟩ := ih
    obtain ⟨lam, hlam, hEl, hprop⟩ := waterfill P hw h1 (y a) (hy a).1 (hy a).2
    have hfsub : ∀ t, ∑ i ∈ insert a s, f i t ≤ D t := fun t => by
      rw [← hfs t]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => hf0 i t)
    have hemp' : ∀ t : Fin n, D t * Ex (stepL a lam P) (ind (t.val + 1)) ≤
        D t - ∑ i ∈ insert a s, f i t := by
      intro t
      have hft := hfsub t
      rw [Ex_stepL]
      rw [Finset.sum_insert has] at hft ⊢
      by_cases hat : a ≤ t
      · have e : ∀ S : Finset (Fin n), (1 - lam S) * ind (t.val + 1) S +
            lam S * ind (t.val + 1) (insert a S) = (1 - lam S) * ind (t.val + 1) S := by
          intro S
          have : ind (t.val + 1) (insert a S) = 0 := by
            unfold ind; rw [if_neg]; push_neg
            exact ⟨a, Finset.mem_insert_self _ _, by have : a.val ≤ t.val := hat; omega⟩
          rw [this]; ring
        rw [Ex_congr' P _ _ e]
        rcases hprop (t.val + 1) (by omega) with hL | hR
        · have e2 : ∀ S : Finset (Fin n), (1 - lam S) * ind (t.val + 1) S = 0 := by
            intro S
            rcases ind_zero_or_one (t.val + 1) S with h | h
            · rw [h]; ring
            · rw [hL _ h]; ring
          rw [Ex_congr' P _ _ e2, Ex_zero, mul_zero]
          linarith
        · have e2 : ∀ S : Finset (Fin n), (1 - lam S) * ind (t.val + 1) S =
              ind (t.val + 1) S - lam S := by
            intro S
            by_cases h0 : lam S = 0
            · rw [h0]; ring
            · rw [hR _ h0]; ring
          rw [Ex_congr' P _ _ e2, Ex_sub, hEl, mul_sub]
          have := hemp t
          have := hcap a t
          linarith
      · have hfa : f a t = 0 := hfl a t (lt_of_not_ge hat)
        have hat' : t.val + 1 ≤ a.val := by
          have : ¬ a.val ≤ t.val := hat
          omega
        have e : ∀ S : Finset (Fin n), (1 - lam S) * ind (t.val + 1) S +
            lam S * ind (t.val + 1) (insert a S) = ind (t.val + 1) S := by
          intro S
          have : ind (t.val + 1) (insert a S) = ind (t.val + 1) S := by
            unfold ind
            simp only [Finset.forall_mem_insert, hat', true_and]
          rw [this]; ring
        rw [Ex_congr' P _ _ e, hfa]
        have := hemp t
        linarith
    refine ⟨stepL a lam P, ?_, ?_, ?_, ?_, hemp', ?_⟩
    · intro q hq
      obtain ⟨p, hp, rfl | rfl⟩ := mem_stepL a lam P q hq
      · exact mul_nonneg (hw p hp) (by linarith [(hlam p.2).2])
      · exact mul_nonneg (hw p hp) (hlam p.2).1
    · rw [Ex_stepL, Ex_congr' P _ (fun _ => (1:ℝ)) (fun S => by ring)]
      exact h1
    · intro q hq
      obtain ⟨p, hp, rfl | rfl⟩ := mem_stepL a lam P q hq
      · exact (hsup p hp).trans (Finset.subset_insert _ _)
      · exact Finset.insert_subset_insert _ (hsup p hp)
    · rw [Ex_stepL, Finset.sum_insert has]
      have e : ∀ S : Finset (Fin n), S ⊆ s →
          (1 - lam S) * (∑ i ∈ S, γ i) + lam S * (∑ i ∈ insert a S, γ i)
            = (∑ i ∈ S, γ i) + γ a * lam S := by
        intro S hS
        rw [Finset.sum_insert (fun ha => has (hS ha))]; ring
      rw [Ex_congr_sub P s hsup _ _ e, Ex_add, Ex_smul, hγ, hEl]; ring
    · intro t ψ hψ
      have hψa : φ a ≤ ψ := hψ a (Finset.mem_insert_self _ _)
      have e : ∀ S : Finset (Fin n), S ⊆ s →
          (1 - lam S) * (D t * V φ S t ψ) + lam S * (D t * V φ (insert a S) t ψ)
            = D t * V φ S t (φ a) + D t * (ψ - φ a) *
              ((1 - lam S) * ind (t.val + 1) S + lam S * ind (t.val + 1) (insert a S)) := by
        intro S hS
        have := scen φ S t ψ (lam S) a (fun ha => has (hS ha))
          (fun i hi => hmax i (hS hi)) hψa
        linear_combination D t * this
      rw [Ex_stepL, Ex_congr_sub P s hsup _ _ e, Ex_add, Ex_smul P (D t * (ψ - φ a)),
        ← Ex_stepL a lam P (ind (t.val + 1))]
      have hc := hcost t (φ a) hmax
      have hm := mul_le_mul_of_nonneg_left (hemp' t) (sub_nonneg.2 hψa)
      simp only [Finset.sum_insert has] at hm ⊢
      linear_combination hc + hm

theorem C2a_holds : C2a_round := by
  intro n D hD f y hf0 hfl hfs hcap hy φ γ
  obtain ⟨P, hw, h1, hsup, hγ, hemp, hcost⟩ :=
    build D f y hf0 hfl hfs hcap hy φ γ Finset.univ
  set ψ : ℝ := ∑ i, |φ i| with hψdef
  have hψ : ∀ i, φ i ≤ ψ := fun i =>
    (le_abs_self _).trans
      (Finset.single_le_sum (fun j _ => abs_nonneg (φ j)) (Finset.mem_univ i))
  set h : Finset (Fin n) → ℝ := fun S => ∑ t, D t * V φ S t ψ + ∑ i ∈ S, γ i with hh
  have hEh : Ex P h ≤ ∑ i, φ i * ∑ t, f i t + ∑ i, γ i * y i := by
    rw [hh, Ex_add, Ex_sum, hγ]
    have h2 : ∀ t ∈ Finset.univ, Ex P (fun S => D t * V φ S t ψ) ≤ ∑ i, φ i * f i t := by
      intro t _
      have := hcost t ψ (fun i _ => hψ i)
      rw [hfs t, sub_self, mul_zero, add_zero] at this
      exact this
    have h3 := Finset.sum_le_sum h2
    have h4 : ∑ t, ∑ i, φ i * f i t = ∑ i, φ i * ∑ t, f i t := by
      rw [Finset.sum_comm]; simp [Finset.mul_sum]
    linarith
  obtain ⟨p, hp, hp0, hpc⟩ := Ex_exists_le P hw h _ h1 hEh
  have hk := Ex_zero_of P hw (fun S => ∑ t, D t * ind (t.val + 1) S)
    (fun S => Finset.sum_nonneg (fun t _ => mul_nonneg (hD t) (ind_nonneg _ _))) (by
      rw [Ex_sum]
      apply Finset.sum_nonpos
      intro t _
      rw [Ex_smul]
      have := hemp t
      rw [hfs t, sub_self] at this
      exact this) p hp hp0
  have hk' : ∑ t, D t * ind (t.val + 1) p.2 = 0 := hk
  have hnull : ∀ t, D t = 0 ∨ ¬ ∀ j ∈ p.2, t.val + 1 ≤ j.val := by
    intro t
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun t _ => mul_nonneg (hD t) (ind_nonneg _ _))).1 hk' t (Finset.mem_univ t)
    rcases mul_eq_zero.1 this with h0 | h0
    · left; exact h0
    · right; intro hG; unfold ind at h0; rw [if_pos hG] at h0; norm_num at h0
  have hsel : ∀ t : Fin n, ∃ j : Fin n,
      D t = 0 ∨ (j ∈ p.2 ∧ j ≤ t ∧ ∀ i ∈ p.2, i ≤ t → φ j ≤ φ i) := by
    intro t
    rcases hnull t with h0 | hG
    · exact ⟨t, Or.inl h0⟩
    · push_neg at hG
      obtain ⟨j0, hj0, hj0t⟩ := hG
      have hne : (p.2.filter (fun i => i ≤ t)).Nonempty :=
        ⟨j0, Finset.mem_filter.2 ⟨hj0, by show j0.val ≤ t.val; omega⟩⟩
      obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image _ φ hne
      rw [Finset.mem_filter] at hj
      exact ⟨j, Or.inr ⟨hj.1, hj.2, fun i hi hit => hmin i (Finset.mem_filter.2 ⟨hi, hit⟩)⟩⟩
  choose sel hsel using hsel
  refine ⟨p.2, fun i t => if i = sel t then D t else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro i t; dsimp only; split_ifs
    · exact hD t
    · exact le_rfl
  · intro i t hti; dsimp only; split_ifs with hi
    · rcases hsel t with h0 | ⟨_, hst, _⟩
      · exact h0
      · exact absurd (show i ≤ t by rw [hi]; exact hst) (not_le.2 hti)
    · rfl
  · intro t; simp
  · intro i t hiS; dsimp only; split_ifs with hi
    · rcases hsel t with h0 | ⟨hs, _, _⟩
      · exact h0
      · exact absurd (show i ∈ p.2 by rw [hi]; exact hs) hiS
    · rfl
  · have hcostg : ∑ i, φ i * ∑ t, (if i = sel t then D t else 0) =
        ∑ t, φ (sel t) * D t := by
      simp only [Finset.mul_sum]; rw [Finset.sum_comm]; simp
    have hpt : ∀ t ∈ Finset.univ, φ (sel t) * D t ≤ D t * V φ p.2 t ψ := by
      intro t _
      rcases hsel t with h0 | ⟨_, _, hmin⟩
      · rw [h0]; simp
      · rw [mul_comm]; apply mul_le_mul_of_nonneg_left _ (hD t)
        unfold V; rw [Finset.le_fold_min]
        exact ⟨hψ _, fun x hx => by rw [Finset.mem_filter] at hx; exact hmin x hx.1 hx.2⟩
    rw [hcostg]
    have := Finset.sum_le_sum hpt
    have hpc' : ∑ t, D t * V φ p.2 t ψ + ∑ i ∈ p.2, γ i ≤
        ∑ i, φ i * ∑ t, f i t + ∑ i, γ i * y i := hpc
    linarith

end C2a

end FLH

theorem solution
    (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t)
    (a : ℝ) (ha : 0 ≤ a) (ha_first : ∀ t : Fin n, t.val = 0 → a ≤ d t)
    (p h q : ℝ) :
    let X : Set ((Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ)) :=
      {z | z.2.1 0 = a ∧ z.2.1 (Fin.last n) = 0 ∧
        (∀ k, 0 ≤ z.2.1 k) ∧
        (∀ i, 0 ≤ z.1 i ∧ (z.2.2 i = 0 ∨ z.2.2 i = 1) ∧
          z.2.1 i.castSucc + z.1 i = d i + z.2.1 i.succ ∧
          z.1 i ≤ (∑ t ∈ Finset.univ.filter (fun t => i ≤ t), d t) * z.2.2 i)}
    let Q := fun (w : Fin n → Fin n → ℝ) (v : Fin (n + 1) → Fin n → ℝ)
        (y : Fin n → ℝ) =>
      (∀ i t, 0 ≤ w i t) ∧ (∀ k t, 0 ≤ v k t) ∧
      (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
      (∀ i t, t < i → w i t = 0) ∧
      (∀ k t, t.val < k.val → v k t = 0) ∧
      (∀ t, v 0 t = if t.val = 0 then a else 0) ∧
      (∀ i t, i ≤ t →
        v i.castSucc t + w i t = (if i = t then d t else 0) + v i.succ t) ∧
      (∀ i t, i ≤ t → w i t ≤ (d t - (if t.val = 0 then a else 0)) * y i)
    let project := fun (w : Fin n → Fin n → ℝ) (v : Fin (n + 1) → Fin n → ℝ)
        (y : Fin n → ℝ) => ((fun i => ∑ t, w i t), (fun k => ∑ t, v k t), y)
    let cost := fun z : (Fin n → ℝ) × (Fin (n + 1) → ℝ) × (Fin n → ℝ) =>
      (∑ i, (p * z.1 i + q * z.2.2 i)) + (∑ i : Fin n, h * z.2.1 i.succ)
    {z | ∃ w v y, Q w v y ∧ z = project w v y} = convexHull ℝ X ∧
      ∃ w v y, Q w v y ∧ (∀ i, y i = 0 ∨ y i = 1) ∧
        (∀ w' v' y', Q w' v' y' → cost (project w v y) ≤ cost (project w' v' y')) ∧
        project w v y ∈ X ∧ (∀ z ∈ X, cost (project w v y) ≤ cost z) := by
  intro X Q project cost
  exact FLH.main_of (FLH.C2_of_C2a FLH.C2a_holds) n hn d hd a ha ha_first p h q
