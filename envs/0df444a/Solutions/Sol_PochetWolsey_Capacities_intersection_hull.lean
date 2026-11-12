-- Prove2me | solution 1 for PochetWolsey.Capacities.intersection_hull
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T07:15:56.22947+00:00
-- url     : https://prove2.me/submissions/4e844fcc-9c2f-4f4e-9530-6564610a77af

import Mathlib
import Definitions.Def_PochetWolsey_Capacities_Model

set_option autoImplicit false

namespace P23c

open MeasureTheory

lemma ceil_mono_real : Monotone (fun u : ℝ => ((⌈u⌉ : ℤ) : ℝ)) :=
  fun _ _ h => by dsimp only; exact_mod_cast Int.ceil_mono h

lemma ceil_sub_anti (x : ℝ) : Antitone (fun l : ℝ => ((⌈x - l⌉ : ℤ) : ℝ)) :=
  fun a b h => by dsimp only; exact_mod_cast Int.ceil_mono (show x - b ≤ x - a by linarith)

lemma floor_add_mono (x : ℝ) : Monotone (fun φ : ℝ => ((⌊x + φ⌋ : ℤ) : ℝ)) :=
  fun a b h => by dsimp only; exact_mod_cast Int.floor_mono (show x + a ≤ x + b by linarith)

lemma integral_ceil_sub (x : ℝ) : ∫ φ in (0:ℝ)..1, ((⌈x - φ⌉ : ℤ) : ℝ) = x := by
  have hc := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1)
    (fun u : ℝ => ((⌈u⌉ : ℤ) : ℝ)) x
  simp only [sub_zero] at hc
  rw [hc]
  have hper : Function.Periodic (fun u : ℝ => ((⌈u⌉ : ℤ) : ℝ) - u) 1 := by
    intro u
    simp only [Int.ceil_add_one, Int.cast_add, Int.cast_one]
    ring
  have h1 := hper.intervalIntegral_add_eq (x - 1) 0
  rw [show x - 1 + 1 = x by ring, zero_add] at h1
  have h2 : ∫ u in (0:ℝ)..1, (((⌈u⌉ : ℤ) : ℝ) - u) = ∫ u in (0:ℝ)..1, ((1:ℝ) - u) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    rw [Set.uIoc_of_le zero_le_one] at hu
    have : ⌈u⌉ = 1 := by
      rw [Int.ceil_eq_iff]; constructor <;> push_cast <;> linarith [hu.1, hu.2]
    simp [this]
  have h3 : ∫ u in (0:ℝ)..1, ((1:ℝ) - u) = 1 / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    simp [integral_id]; norm_num
  have hsplit : ∫ u in (x - 1)..x, (((⌈u⌉ : ℤ) : ℝ) - u) =
      (∫ u in (x - 1)..x, ((⌈u⌉ : ℤ) : ℝ)) - ∫ u in (x - 1)..x, u :=
    intervalIntegral.integral_sub (ceil_mono_real.intervalIntegrable)
      intervalIntegral.intervalIntegrable_id
  have hid : ∫ u in (x - 1)..x, u = x - 1 / 2 := by rw [integral_id]; ring
  linarith

lemma integral_floor_add (x : ℝ) : ∫ φ in (0:ℝ)..1, ((⌊x + φ⌋ : ℤ) : ℝ) = x := by
  have : ∀ φ : ℝ, ((⌊x + φ⌋ : ℤ) : ℝ) = -((⌈-x - φ⌉ : ℤ) : ℝ) := by
    intro φ; rw [show -x - φ = -(x + φ) by ring, Int.ceil_neg]; push_cast; ring
  simp_rw [this]
  rw [intervalIntegral.integral_neg, integral_ceil_sub]; ring

variable {n : ℕ}

noncomputable def H (C : ℝ) (d : Fin n → ℝ) (k : Fin n) (l : ℝ) (y : Fin n → ℝ) : ℝ :=
  max 0 (Finset.univ.sup' ⟨k, Finset.mem_univ k⟩ (fun t : Fin n =>
    if k ≤ t then ((⌈(∑ u ∈ Finset.Icc k t, d u) / C - l⌉ : ℤ) : ℝ) - ∑ u ∈ Finset.Icc k t, y u
    else 0))

lemma H_nonneg (C : ℝ) (d : Fin n → ℝ) (k : Fin n) (l : ℝ) (y : Fin n → ℝ) :
    0 ≤ H C d k l y := le_max_left _ _

lemma H_ge (C : ℝ) (d : Fin n → ℝ) (k : Fin n) (l : ℝ) (y : Fin n → ℝ) (t : Fin n)
    (hkt : k ≤ t) :
    ((⌈(∑ u ∈ Finset.Icc k t, d u) / C - l⌉ : ℤ) : ℝ) - ∑ u ∈ Finset.Icc k t, y u
      ≤ H C d k l y := by
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ t))
  simp [hkt]

lemma H_le (C : ℝ) (d : Fin n → ℝ) (k : Fin n) (l : ℝ) (y : Fin n → ℝ) (R : ℝ) (h0 : 0 ≤ R)
    (ht : ∀ t, k ≤ t → ((⌈(∑ u ∈ Finset.Icc k t, d u) / C - l⌉ : ℤ) : ℝ)
      - ∑ u ∈ Finset.Icc k t, y u ≤ R) :
    H C d k l y ≤ R := by
  refine max_le h0 (Finset.sup'_le _ _ (fun t _ => ?_))
  split_ifs with hkt
  · exact ht t hkt
  · exact h0

lemma H_anti (C : ℝ) (d : Fin n → ℝ) (k : Fin n) (y : Fin n → ℝ) :
    Antitone (fun l => H C d k l y) := by
  intro l1 l2 h
  refine H_le C d k l2 y _ (H_nonneg C d k l1 y) ?_
  intro t hkt
  refine le_trans ?_ (H_ge C d k l1 y t hkt)
  have h1 : ⌈(∑ u ∈ Finset.Icc k t, d u) / C - l2⌉ ≤ ⌈(∑ u ∈ Finset.Icc k t, d u) / C - l1⌉ :=
    Int.ceil_mono (by linarith)
  have h2 : ((⌈(∑ u ∈ Finset.Icc k t, d u) / C - l2⌉ : ℤ) : ℝ)
      ≤ ((⌈(∑ u ∈ Finset.Icc k t, d u) / C - l1⌉ : ℤ) : ℝ) := by exact_mod_cast h1
  linarith

noncomputable def G (C : ℝ) (d : Fin n → ℝ) (k : Fin n) (y : Fin n → ℝ) : ℝ :=
  ∫ l in (0:ℝ)..1, H C d k l y

lemma H_int (C : ℝ) (d : Fin n → ℝ) (k : Fin n) (y : Fin n → ℝ) :
    IntervalIntegrable (fun l => H C d k l y) volume 0 1 :=
  (H_anti C d k y).intervalIntegrable

lemma G_nonneg (C : ℝ) (d : Fin n → ℝ) (k : Fin n) (y : Fin n → ℝ) : 0 ≤ G C d k y :=
  intervalIntegral.integral_nonneg zero_le_one (fun l _ => H_nonneg C d k l y)

lemma G_ge (C : ℝ) (d : Fin n → ℝ) (k : Fin n) (y : Fin n → ℝ) (t : Fin n) (hkt : k ≤ t) :
    (∑ u ∈ Finset.Icc k t, d u) / C - ∑ u ∈ Finset.Icc k t, y u ≤ G C d k y := by
  set b := (∑ u ∈ Finset.Icc k t, d u) / C
  set Y := ∑ u ∈ Finset.Icc k t, y u
  have hanti : Antitone (fun l : ℝ => ((⌈b - l⌉ : ℤ) : ℝ)) := ceil_sub_anti b
  have hi : IntervalIntegrable (fun l : ℝ => ((⌈b - l⌉ : ℤ) : ℝ) - Y) volume 0 1 :=
    hanti.intervalIntegrable.sub intervalIntegrable_const
  have he : ∫ l in (0:ℝ)..1, (((⌈b - l⌉ : ℤ) : ℝ) - Y) = b - Y := by
    rw [intervalIntegral.integral_sub hanti.intervalIntegrable intervalIntegrable_const,
      integral_ceil_sub]
    simp
  rw [← he]
  exact intervalIntegral.integral_mono_on zero_le_one hi (H_int C d k y)
    (fun l _ => H_ge C d k l y t hkt)

lemma sum_int_of_binary (y : Fin n → ℝ) (hy : ∀ u, y u = 0 ∨ y u = 1) (s : Finset (Fin n)) :
    ∃ m : ℤ, ∑ u ∈ s, y u = m := by
  refine ⟨∑ u ∈ s, (if y u = 1 then (1:ℤ) else 0), ?_⟩
  push_cast
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rcases hy u with h | h <;> simp [h]

lemma G_le_of_mem (C : ℝ) (hC : 0 < C) (d : Fin n → ℝ) (k : Fin n) (y : Fin n → ℝ)
    (hy : ∀ u, y u = 0 ∨ y u = 1) (s : ℝ) (hs : 0 ≤ s)
    (hcov : ∀ t, k ≤ t → (∑ u ∈ Finset.Icc k t, d u) ≤ s + C * ∑ u ∈ Finset.Icc k t, y u) :
    C * G C d k y ≤ s := by
  have hanti : Antitone (fun l : ℝ => ((⌈s / C - l⌉ : ℤ) : ℝ)) := ceil_sub_anti (s / C)
  have hle : G C d k y ≤ s / C := by
    rw [← integral_ceil_sub (s / C)]
    refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one (H_int C d k y)
      hanti.intervalIntegrable (fun l hl => ?_)
    have hsC : 0 ≤ s / C := div_nonneg hs hC.le
    refine H_le C d k l y _ ?_ ?_
    · have : (0:ℤ) ≤ ⌈s / C - l⌉ := by
        rw [Int.le_ceil_iff]; push_cast; linarith [hl.2]
      exact_mod_cast this
    · intro t hkt
      obtain ⟨m, hm⟩ := sum_int_of_binary y hy (Finset.Icc k t)
      rw [hm]
      have hb : (∑ u ∈ Finset.Icc k t, d u) / C - m ≤ s / C := by
        have := hcov t hkt
        rw [hm] at this
        rw [div_sub' hC.ne', div_le_div_iff_of_pos_right hC]
        linarith
      have h1 : ⌈(∑ u ∈ Finset.Icc k t, d u) / C - l⌉ - m ≤ ⌈s / C - l⌉ := by
        rw [← Int.ceil_sub_intCast]
        exact Int.ceil_mono (by linarith)
      have h2 : ((⌈(∑ u ∈ Finset.Icc k t, d u) / C - l⌉ - m : ℤ) : ℝ) ≤ ⌈s / C - l⌉ := by
        exact_mod_cast h1
      push_cast at h2
      exact h2
  have := mul_le_mul_of_nonneg_left hle hC.le
  rwa [mul_div_cancel₀ s hC.ne'] at this

lemma G_convex (C : ℝ) (d : Fin n → ℝ) (k : Fin n) (y1 y2 : Fin n → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    G C d k (a • y1 + b • y2) ≤ a * G C d k y1 + b * G C d k y2 := by
  have hpt : ∀ l, H C d k l (a • y1 + b • y2) ≤ a * H C d k l y1 + b * H C d k l y2 := by
    intro l
    refine H_le C d k l _ _ (by positivity [H_nonneg C d k l y1, H_nonneg C d k l y2]) ?_
    intro t hkt
    have e1 := mul_le_mul_of_nonneg_left (H_ge C d k l y1 t hkt) ha
    have e2 := mul_le_mul_of_nonneg_left (H_ge C d k l y2 t hkt) hb
    have hs : ∑ u ∈ Finset.Icc k t, (a • y1 + b • y2) u
        = a * ∑ u ∈ Finset.Icc k t, y1 u + b * ∑ u ∈ Finset.Icc k t, y2 u := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hs]
    set c := ((⌈(∑ u ∈ Finset.Icc k t, d u) / C - l⌉ : ℤ) : ℝ)
    have hc : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    nlinarith
  unfold G
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((H_int C d k y1).const_mul a)
      ((H_int C d k y2).const_mul b)]
  exact intervalIntegral.integral_mono_on zero_le_one (H_int C d k _)
    (((H_int C d k y1).const_mul a).add ((H_int C d k y2).const_mul b)) (fun l _ => hpt l)

/-! cumulative sums (from WWHullAux, 8897fedf) -/

noncomputable def cum (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun i => ∑ u : Fin n, if u.castSucc < i then y u else 0

lemma cum_zero (y : Fin n → ℝ) : cum y 0 = 0 := by
  simp [cum]

lemma cum_step (y : Fin n → ℝ) (i : Fin n) : cum y i.succ - cum y i.castSucc = y i := by
  have h : ∀ u : Fin n, ((if u.castSucc < i.succ then y u else 0) -
      (if u.castSucc < i.castSucc then y u else 0)) = if u = i then y u else 0 := by
    intro u
    have hv : u = i ↔ u.val = i.val := Fin.ext_iff
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, hv]
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp only [cum]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun u _ => h u), Finset.sum_ite_eq']
  simp

lemma sum_Icc_eq (y : Fin n → ℝ) (k j : Fin n) (hkj : k ≤ j) :
    ∑ u ∈ Finset.Icc k j, y u = cum y j.succ - cum y k.castSucc := by
  have hkj' : k.val ≤ j.val := hkj
  have h : ∀ u : Fin n, ((if u.castSucc < j.succ then y u else 0) -
      (if u.castSucc < k.castSucc then y u else 0)) =
        if u ∈ Finset.Icc k j then y u else 0 := by
    intro u
    simp only [Finset.mem_Icc, Fin.le_iff_val_le_val, Fin.lt_def, Fin.val_castSucc,
      Fin.val_succ]
    split_ifs <;> first | ring1 | (exfalso; omega)
  simp only [cum]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun u _ => h u), Finset.sum_ite_mem,
    Finset.univ_inter]

lemma cum_tele (F : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    cum (fun u => F u.succ - F u.castSucc) i = F i - F 0 := by
  induction i using Fin.induction with
  | zero => rw [cum_zero]; ring
  | succ i ih =>
    have := cum_step (fun u => F u.succ - F u.castSucc) i
    linarith

lemma sum_Icc_tele (F : Fin (n + 1) → ℝ) (k j : Fin n) (hkj : k ≤ j) :
    ∑ u ∈ Finset.Icc k j, (F u.succ - F u.castSucc) = F j.succ - F k.castSucc := by
  rw [sum_Icc_eq (fun u => F u.succ - F u.castSucc) k j hkj, cum_tele, cum_tele]
  ring

/-! threshold rounding -/

noncomputable def rnd (c : Fin (n + 1) → ℝ) (φ : ℝ) : Fin n → ℤ :=
  fun u => ⌊c u.succ + φ⌋ - ⌊c u.castSucc + φ⌋

def V (n : ℕ) : Finset (Fin n → ℤ) := Fintype.piFinset (fun _ => ({0, 1} : Finset ℤ))

lemma rnd_mem (y : Fin n → ℝ) (hy : ∀ u, 0 ≤ y u ∧ y u ≤ 1) (φ : ℝ) :
    rnd (cum y) φ ∈ V n := by
  rw [V, Fintype.mem_piFinset]
  intro u
  have hs := cum_step y u
  have he : cum y u.succ + φ = (cum y u.castSucc + φ) + y u := by linarith
  simp only [rnd, he]
  have h1 : ⌊cum y u.castSucc + φ⌋ ≤ ⌊(cum y u.castSucc + φ) + y u⌋ :=
    Int.floor_mono (by linarith [(hy u).1])
  have h2 : ⌊(cum y u.castSucc + φ) + y u⌋ ≤ ⌊cum y u.castSucc + φ⌋ + 1 := by
    rw [← Int.floor_add_one]; exact Int.floor_mono (by linarith [(hy u).2])
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma rnd_meas (c : Fin (n + 1) → ℝ) : Measurable (rnd c) := by
  rw [measurable_pi_iff]
  intro u
  have hsub : Measurable (fun p : ℤ × ℤ => p.1 - p.2) := measurable_of_countable _
  exact hsub.comp (((measurable_const_add (c u.succ)).floor).prodMk
    ((measurable_const_add (c u.castSucc)).floor))

noncomputable def ω (c : Fin (n + 1) → ℝ) (w : Fin n → ℤ) : ℝ :=
  ∫ φ in (0:ℝ)..1, (if rnd c φ = w then (1:ℝ) else 0)

lemma ind_int (c : Fin (n + 1) → ℝ) (w : Fin n → ℤ) :
    IntervalIntegrable (fun φ => if rnd c φ = w then (1:ℝ) else 0) volume 0 1 := by
  have hm : MeasurableSet {φ | rnd c φ = w} := (rnd_meas c) (measurableSet_singleton w)
  refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun ?_ ?_
  · exact (Measurable.ite hm measurable_const measurable_const).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun φ => ?_)
    simp only
    split_ifs <;> simp

lemma ω_nonneg (c : Fin (n + 1) → ℝ) (w : Fin n → ℤ) : 0 ≤ ω c w :=
  intervalIntegral.integral_nonneg zero_le_one (fun φ _ => by split_ifs <;> norm_num)

lemma comp_eq (y : Fin n → ℝ) (hy : ∀ u, 0 ≤ y u ∧ y u ≤ 1) (g : (Fin n → ℤ) → ℝ) :
    (fun φ => g (rnd (cum y) φ)) =
      fun φ => ∑ w ∈ V n, (if rnd (cum y) φ = w then (1:ℝ) else 0) * g w := by
  funext φ
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (rnd_mem y hy φ)]

lemma comp_int (y : Fin n → ℝ) (hy : ∀ u, 0 ≤ y u ∧ y u ≤ 1) (g : (Fin n → ℤ) → ℝ) :
    IntervalIntegrable (fun φ => g (rnd (cum y) φ)) volume 0 1 := by
  rw [comp_eq y hy g]
  simpa only [Finset.sum_fn] using
    IntervalIntegrable.sum (V n) (fun w _ => (ind_int (cum y) w).mul_const (g w))

lemma integral_comp (y : Fin n → ℝ) (hy : ∀ u, 0 ≤ y u ∧ y u ≤ 1) (g : (Fin n → ℤ) → ℝ) :
    ∫ φ in (0:ℝ)..1, g (rnd (cum y) φ) = ∑ w ∈ V n, ω (cum y) w * g w := by
  rw [comp_eq y hy g, intervalIntegral.integral_finsetSum
    (fun w _ => (ind_int (cum y) w).mul_const _)]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [intervalIntegral.integral_mul_const]
  rfl

lemma H_rnd_le (C : ℝ) (d : Fin n → ℝ) (k : Fin n) (l : ℝ) (y : Fin n → ℝ) (φ : ℝ) :
    H C d k l (fun u => ((rnd (cum y) φ u : ℤ) : ℝ)) ≤
      ((⌊cum y k.castSucc + φ⌋ : ℤ) : ℝ)
        + ((⌈(H C d k l y - cum y k.castSucc) - φ⌉ : ℤ) : ℝ) := by
  set M := H C d k l y
  set ck := cum y k.castSucc
  refine H_le C d k l _ _ ?_ ?_
  · have hM := H_nonneg C d k l y
    have hf := Int.sub_one_lt_floor (ck + φ)
    have : -⌊ck + φ⌋ ≤ ⌈(M - ck) - φ⌉ := by
      rw [Int.le_ceil_iff]; push_cast; linarith
    have : (0:ℤ) ≤ ⌊ck + φ⌋ + ⌈(M - ck) - φ⌉ := by omega
    exact_mod_cast this
  · intro t hkt
    have hsum : ∑ u ∈ Finset.Icc k t, ((rnd (cum y) φ u : ℤ) : ℝ)
        = ((⌊cum y t.succ + φ⌋ : ℤ) : ℝ) - ((⌊ck + φ⌋ : ℤ) : ℝ) := by
      have := sum_Icc_tele (fun i => ((⌊cum y i + φ⌋ : ℤ) : ℝ)) k t hkt
      rw [← this]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      simp [rnd]
    rw [hsum]
    have Ht := H_ge C d k l y t hkt
    rw [sum_Icc_eq y k t hkt] at Ht
    set A := ⌈(∑ u ∈ Finset.Icc k t, d u) / C - l⌉
    have hf := Int.sub_one_lt_floor (cum y t.succ + φ)
    have : A - ⌊cum y t.succ + φ⌋ ≤ ⌈(M - ck) - φ⌉ := by
      rw [Int.le_ceil_iff]; push_cast; linarith
    have h2 : ((A - ⌊cum y t.succ + φ⌋ : ℤ) : ℝ) ≤ ((⌈(M - ck) - φ⌉ : ℤ) : ℝ) := by
      exact_mod_cast this
    push_cast at h2
    linarith

lemma round_le (C : ℝ) (d : Fin n → ℝ) (k : Fin n) (y : Fin n → ℝ)
    (hy : ∀ u, 0 ≤ y u ∧ y u ≤ 1) :
    ∑ w ∈ V n, ω (cum y) w * G C d k (fun u => ((w u : ℤ) : ℝ)) ≤ G C d k y := by
  have hswap : ∑ w ∈ V n, ω (cum y) w * G C d k (fun u => ((w u : ℤ) : ℝ))
      = ∫ l in (0:ℝ)..1, ∑ w ∈ V n, ω (cum y) w * H C d k l (fun u => ((w u : ℤ) : ℝ)) := by
    rw [intervalIntegral.integral_finsetSum
      (fun w _ => (H_int C d k (fun u => ((w u : ℤ) : ℝ))).const_mul _)]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [intervalIntegral.integral_const_mul]
    rfl
  rw [hswap]
  have hint : IntervalIntegrable
      (fun l => ∑ w ∈ V n, ω (cum y) w * H C d k l (fun u => ((w u : ℤ) : ℝ))) volume 0 1 :=
    by
      simpa only [Finset.sum_fn] using IntervalIntegrable.sum (V n)
        (fun w _ => (H_int C d k (fun u => ((w u : ℤ) : ℝ))).const_mul (ω (cum y) w))
  refine intervalIntegral.integral_mono_on zero_le_one hint (H_int C d k y) (fun l _ => ?_)
  have hc := integral_comp y hy (fun w => H C d k l (fun u => ((w u : ℤ) : ℝ)))
  try simp only at hc
  rw [← hc]
  set ck := cum y k.castSucc
  have hR : IntervalIntegrable (fun φ : ℝ => ((⌊ck + φ⌋ : ℤ) : ℝ)
      + ((⌈(H C d k l y - ck) - φ⌉ : ℤ) : ℝ)) volume 0 1 := by
    have h1 := floor_add_mono ck
    have h2 := ceil_sub_anti (H C d k l y - ck)
    exact h1.intervalIntegrable.add h2.intervalIntegrable
  have hval : ∫ φ in (0:ℝ)..1, (((⌊ck + φ⌋ : ℤ) : ℝ)
      + ((⌈(H C d k l y - ck) - φ⌉ : ℤ) : ℝ)) = H C d k l y := by
    have h1 := floor_add_mono ck
    have h2 := ceil_sub_anti (H C d k l y - ck)
    rw [intervalIntegral.integral_add h1.intervalIntegrable h2.intervalIntegrable,
      integral_floor_add, integral_ceil_sub]
    ring
  rw [← hval]
  exact intervalIntegral.integral_mono_on zero_le_one
    (comp_int y hy (fun w => H C d k l (fun u => ((w u : ℤ) : ℝ)))) hR
    (fun φ _ => H_rnd_le C d k l y φ)

lemma mean_eq (y : Fin n → ℝ) (hy : ∀ u, 0 ≤ y u ∧ y u ≤ 1) (u : Fin n) :
    ∑ w ∈ V n, ω (cum y) w * ((w u : ℤ) : ℝ) = y u := by
  have hc := integral_comp y hy (fun w => ((w u : ℤ) : ℝ))
  try simp only at hc
  rw [← hc]
  simp only [rnd, Int.cast_sub]
  have h1 := floor_add_mono (cum y u.succ)
  have h2 := floor_add_mono (cum y u.castSucc)
  rw [intervalIntegral.integral_sub h1.intervalIntegrable h2.intervalIntegrable,
    integral_floor_add, integral_floor_add, cum_step]

lemma weight_sum (y : Fin n → ℝ) (hy : ∀ u, 0 ≤ y u ∧ y u ≤ 1) :
    ∑ w ∈ V n, ω (cum y) w = 1 := by
  have hc := integral_comp y hy (fun _ => (1:ℝ))
  simp only [mul_one] at hc
  rw [← hc]
  simp

end P23c

theorem solution {n : ℕ} (hn : 0 < n) (C : ℝ) (hC : 0 < C)
    (d : Fin n → ℝ) (hd : ∀ t, 0 ≤ d t ∧ d t ≤ C) :
    convexHull ℝ
      {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) |
        (∀ j, 0 ≤ p.1 j) ∧ (∀ u, p.2 u = 0 ∨ p.2 u = 1) ∧
        ∀ k t, k ≤ t → (∑ u ∈ Finset.Icc k t, d u) ≤
          p.1 k.castSucc + C * ∑ u ∈ Finset.Icc k t, p.2 u} =
    ⋂ k : Fin n, convexHull ℝ
      {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) |
        (∀ j, 0 ≤ p.1 j) ∧ (∀ u, p.2 u = 0 ∨ p.2 u = 1) ∧
        ∀ t, k ≤ t → (∑ u ∈ Finset.Icc k t, d u) ≤
          p.1 k.castSucc + C * ∑ u ∈ Finset.Icc k t, p.2 u} := by
  apply Set.Subset.antisymm
  · refine Set.subset_iInter (fun k => convexHull_mono ?_)
    rintro p ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t hkt => h3 k t hkt⟩
  · intro p hp
    rw [Set.mem_iInter] at hp
    have key : ∀ k : Fin n, (∀ j, 0 ≤ p.1 j) ∧ (∀ u, 0 ≤ p.2 u ∧ p.2 u ≤ 1) ∧
        C * P23c.G C d k p.2 ≤ p.1 k.castSucc := by
      intro k
      refine convexHull_min (t := {q : (Fin (n + 1) → ℝ) × (Fin n → ℝ) |
        (∀ j, 0 ≤ q.1 j) ∧ (∀ u, 0 ≤ q.2 u ∧ q.2 u ≤ 1) ∧
        C * P23c.G C d k q.2 ≤ q.1 k.castSucc}) ?_ ?_ (hp k)
      · rintro q ⟨h1, h2, h3⟩
        refine ⟨h1, fun u => ?_, P23c.G_le_of_mem C hC d k q.2 h2 _ (h1 _) h3⟩
        rcases h2 u with h | h <;> rw [h] <;> norm_num
      · intro q1 hq1 q2 hq2 a b ha hb hab
        obtain ⟨a1, a2, a3⟩ := hq1
        obtain ⟨b1, b2, b3⟩ := hq2
        refine ⟨fun j => ?_, fun u => ?_, ?_⟩
        · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          nlinarith [a1 j, b1 j]
        · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          constructor <;> nlinarith [a2 u, b2 u]
        · have hg := P23c.G_convex C d k q1.2 q2.2 a b ha hb hab
          simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul]
          nlinarith [mul_le_mul_of_nonneg_left a3 ha, mul_le_mul_of_nonneg_left b3 hb]
    have hbox := (key ⟨0, hn⟩).2.1
    have hs0 := (key ⟨0, hn⟩).1
    set y := p.2 with hy
    set s := p.1 with hs
    set E : Fin n → ℝ := fun k =>
      ∑ w ∈ P23c.V n, P23c.ω (P23c.cum y) w * P23c.G C d k (fun u => ((w u : ℤ) : ℝ)) with hE
    have hEle : ∀ k, E k ≤ P23c.G C d k y := fun k => P23c.round_le C d k y hbox
    set e : Fin (n + 1) → (Fin n → ℤ) → ℝ := fun j w =>
      if h : j.val < n then
        C * P23c.G C d ⟨j.val, h⟩ (fun u => ((w u : ℤ) : ℝ)) - C * E ⟨j.val, h⟩
      else 0 with he
    set z : (Fin n → ℤ) → (Fin (n + 1) → ℝ) × (Fin n → ℝ) :=
      fun w => (fun j => s j + e j w, fun u => ((w u : ℤ) : ℝ)) with hz
    have hecast : ∀ (k : Fin n) w, e k.castSucc w =
        C * P23c.G C d k (fun u => ((w u : ℤ) : ℝ)) - C * E k := by
      intro k w
      simp only [he, Fin.val_castSucc, k.isLt, dif_pos]
    have hmem : ∀ w ∈ P23c.V n, z w ∈ {p : (Fin (n + 1) → ℝ) × (Fin n → ℝ) |
        (∀ j, 0 ≤ p.1 j) ∧ (∀ u, p.2 u = 0 ∨ p.2 u = 1) ∧
        ∀ k t, k ≤ t → (∑ u ∈ Finset.Icc k t, d u) ≤
          p.1 k.castSucc + C * ∑ u ∈ Finset.Icc k t, p.2 u} := by
      intro w hw
      rw [P23c.V, Fintype.mem_piFinset] at hw
      refine ⟨fun j => ?_, fun u => ?_, fun k t hkt => ?_⟩
      · show 0 ≤ s j + e j w
        by_cases hj : j.val < n
        · set k : Fin n := ⟨j.val, hj⟩
          have hjk : j = k.castSucc := Fin.ext rfl
          rw [hjk, hecast]
          have h1 := (key k).2.2
          have h2 := mul_le_mul_of_nonneg_left (hEle k) hC.le
          have h3 := mul_nonneg hC.le (P23c.G_nonneg C d k (fun u => ((w u : ℤ) : ℝ)))
          linarith
        · simp only [he, hj, dif_neg, not_false_eq_true, add_zero]
          exact hs0 j
      · show ((w u : ℤ) : ℝ) = 0 ∨ ((w u : ℤ) : ℝ) = 1
        have := hw u
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h <;> simp [h]
      · show (∑ u ∈ Finset.Icc k t, d u) ≤
          (s k.castSucc + e k.castSucc w) + C * ∑ u ∈ Finset.Icc k t, ((w u : ℤ) : ℝ)
        rw [hecast]
        have h1 := (key k).2.2
        have h2 := mul_le_mul_of_nonneg_left (hEle k) hC.le
        have h3 := mul_le_mul_of_nonneg_left
          (P23c.G_ge C d k (fun u => ((w u : ℤ) : ℝ)) t hkt) hC.le
        rw [mul_sub, mul_div_cancel₀ _ hC.ne'] at h3
        linarith
    have hpz : p = ∑ w ∈ P23c.V n, P23c.ω (P23c.cum y) w • z w := by
      have hw1 := P23c.weight_sum y hbox
      refine Prod.ext ?_ ?_
      · funext j
        rw [Prod.fst_sum, Finset.sum_apply]
        simp only [hz, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, mul_add,
          Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
        suffices hsum : ∑ w ∈ P23c.V n, P23c.ω (P23c.cum y) w * e j w = 0 by
          rw [hsum, add_zero]
        by_cases hj : j.val < n
        · simp only [he, hj, dif_pos, mul_sub, Finset.sum_sub_distrib]
          rw [← Finset.sum_mul, hw1, one_mul]
          simp only [hE]
          rw [Finset.mul_sum]
          simp only [mul_left_comm]
          ring
        · simp [he, hj]
      · funext u
        rw [Prod.snd_sum, Finset.sum_apply]
        simp only [hz, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
        exact (P23c.mean_eq y hbox u).symm
    rw [hpz]
    exact (convex_convexHull ℝ _).sum_mem (fun w _ => P23c.ω_nonneg _ w)
      (P23c.weight_sum y hbox) (fun w hw => subset_convexHull ℝ _ (hmem w hw))
