-- Prove2me | solution 1 for RobustBooking.TwoFare.ppl_ratio
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:26:39.28121+00:00
-- url     : https://prove2.me/submissions/f3745211-c321-44be-90d0-4056c97c7b38

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_BookingPolicies

namespace Aux_RB_ppl

open RobustBooking.TwoFare

def instHigh (n : ℝ) (hn : 0 < n) : List Request :=
  [⟨.high, n, hn⟩]

lemma rev_nonneg (f₁ f₂ n : ℝ) (h1 : 0 ≤ f₁) (h2 : 0 ≤ f₂) (A : DetPolicy) :
    ∀ (I : List Request) (hist : List (Request × ℝ)) (used : ℝ),
      0 ≤ (List.zipWith (fun q a => fare f₁ f₂ q.cls * a) I (runFrom n A hist used I)).sum := by
  intro I
  induction I with
  | nil => intro hist used; simp [runFrom]
  | cons q rest ih =>
    intro hist used
    simp only [runFrom, List.zipWith_cons_cons, List.sum_cons]
    have hf : 0 ≤ fare f₁ f₂ q.cls := by cases q.cls <;> simp [fare, h1, h2]
    exact add_nonneg (mul_nonneg hf (le_max_left _ _)) (ih _ _)

lemma opt2 (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hn : 0 < n) :
    optRevenue f₁ f₂ n (instI2 n hn) = f₂ * n := by
  unfold optRevenue
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun _ => n, ⟨fun i => ⟨hn.le, ?_⟩, ?_⟩, ?_⟩
    · have : i = (⟨0, by simp [instI2]⟩ : Fin (instI2 n hn).length) := Fin.ext (by
        have := i.isLt; simp [instI2] at this; omega)
      subst this; exact le_rfl
    · show ∑ _i : Fin 1, n ≤ n
      simp
    · show f₂ * n = ∑ i : Fin 1, fare f₁ f₂ ((instI2 n hn).get i).cls * n
      simp [instI2, fare]
  · rintro v ⟨x, ⟨hx1, hx2⟩, rfl⟩
    calc ∑ i, fare f₁ f₂ ((instI2 n hn).get i).cls * x i ≤ ∑ i, f₂ * x i := by
          refine Finset.sum_le_sum fun i _ => ?_
          have : i = (⟨0, by simp [instI2]⟩ : Fin (instI2 n hn).length) := Fin.ext (by
            have := i.isLt; simp [instI2] at this; omega)
          subst this
          simp [instI2, fare]
      _ = f₂ * ∑ i, x i := (Finset.mul_sum _ _ _).symm
      _ ≤ f₂ * n := mul_le_mul_of_nonneg_left hx2 hf₂.le

lemma optHigh (f₁ f₂ n : ℝ) (hf₁ : 0 < f₁) (hn : 0 < n) :
    optRevenue f₁ f₂ n (instHigh n hn) = f₁ * n := by
  unfold optRevenue
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun _ => n, ⟨fun i => ⟨hn.le, ?_⟩, ?_⟩, ?_⟩
    · have : i = (⟨0, by simp [instHigh]⟩ : Fin (instHigh n hn).length) := Fin.ext (by
        have := i.isLt; simp [instHigh] at this; omega)
      subst this; exact le_rfl
    · show ∑ _i : Fin 1, n ≤ n
      simp
    · show f₁ * n = ∑ i : Fin 1, fare f₁ f₂ ((instHigh n hn).get i).cls * n
      simp [instHigh, fare]
  · rintro v ⟨x, ⟨hx1, hx2⟩, rfl⟩
    calc ∑ i, fare f₁ f₂ ((instHigh n hn).get i).cls * x i ≤ ∑ i, f₁ * x i := by
          refine Finset.sum_le_sum fun i _ => ?_
          have : i = (⟨0, by simp [instHigh]⟩ : Fin (instHigh n hn).length) := Fin.ext (by
            have := i.isLt; simp [instHigh] at this; omega)
          subst this
          simp [instHigh, fare]
      _ = f₁ * ∑ i, x i := (Finset.mul_sum _ _ _).symm
      _ ≤ f₁ * n := mul_le_mul_of_nonneg_left hx2 hf₁.le

lemma rev_ppl_instI2 (f₁ f₂ n θ₁ : ℝ) (hn : 0 < n) (hθ0 : 0 ≤ θ₁) (hθn : θ₁ ≤ n) :
    revenue f₁ f₂ n (ppl n θ₁) (instI2 n hn) = f₂ * (n - θ₁) := by
  simp only [revenue, accepted, runFrom, instI2, ppl, acceptedOfClass, fare,
    List.filter_nil, List.map_nil, List.sum_nil, sub_zero, min_self,
    List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, add_zero]
  have hmin : min (n - θ₁) n = n - θ₁ := min_eq_left (by linarith)
  have hmax : max 0 (n - θ₁) = n - θ₁ := max_eq_right (by linarith)
  rw [hmin, hmax]

lemma rev_ppl_instHigh (f₁ f₂ n θ₁ : ℝ) (hn : 0 < n) (hθ0 : 0 ≤ θ₁) (hθn : θ₁ ≤ n) :
    revenue f₁ f₂ n (ppl n θ₁) (instHigh n hn) = f₁ * θ₁ := by
  simp only [revenue, accepted, runFrom, instHigh, ppl, acceptedOfClass, fare,
    List.filter_nil, List.map_nil, List.sum_nil, sub_zero, min_self,
    List.zipWith_cons_cons, List.zipWith_nil_right, List.sum_cons, add_zero]
  have hmin : min θ₁ n = θ₁ := min_eq_left hθn
  have hmax : max 0 θ₁ = θ₁ := max_eq_right hθ0
  rw [hmin, hmax]

lemma acceptedOfClass_append (c : FareClass) (hist : List (Request × ℝ)) (q : Request) (a : ℝ) :
    acceptedOfClass c (hist ++ [(q, a)]) =
      acceptedOfClass c hist + (if q.cls = c then a else 0) := by
  unfold acceptedOfClass
  rw [List.filter_append, List.map_append, List.sum_append]
  by_cases h : q.cls = c
  · simp [h]
  · simp [h]

def qtyOfClass (c : FareClass) (I : List Request) : ℝ :=
  ((I.filter (fun q => decide (q.cls = c))).map Request.qty).sum

lemma qtyOfClass_nil (c : FareClass) : qtyOfClass c [] = 0 := by
  simp [qtyOfClass]

lemma qtyOfClass_cons (c : FareClass) (q : Request) (rest : List Request) :
    qtyOfClass c (q :: rest) = (if q.cls = c then q.qty else 0) + qtyOfClass c rest := by
  unfold qtyOfClass
  by_cases h : q.cls = c <;> simp [h]

lemma qtyOfClass_nonneg (c : FareClass) : ∀ I : List Request, 0 ≤ qtyOfClass c I
  | [] => by simp [qtyOfClass]
  | q :: rest => by
    rw [qtyOfClass_cons]
    split_ifs
    · exact add_nonneg q.qty_pos.le (qtyOfClass_nonneg c rest)
    · exact add_nonneg le_rfl (qtyOfClass_nonneg c rest)

lemma min_add_min_sub (q S C : ℝ) (hS : 0 ≤ S) :
    min q C + min S (C - min q C) = min (q + S) C := by
  rcases le_total q C with h1 | h1 <;> rcases le_total (q + S) C with h2 | h2
  · have h3 : S ≤ C - q := by linarith
    rw [min_eq_left h1, min_eq_left h3, min_eq_left h2]
  · have h3 : C - q ≤ S := by linarith
    rw [min_eq_left h1, min_eq_right h3, min_eq_right h2]
    ring
  · rw [min_eq_right h1, sub_self, min_eq_left h2]
    have h3 : S ≤ 0 := by linarith
    rw [min_eq_left h3]
    linarith
  · rw [min_eq_right h1, sub_self, min_eq_right h2, min_eq_right hS, add_zero]

lemma ppl_runFrom_eq (f₁ f₂ n θ₁ : ℝ) :
    ∀ (I : List Request) (hist : List (Request × ℝ)) (used : ℝ),
      acceptedOfClass .high hist ≤ θ₁ →
      acceptedOfClass .low hist ≤ n - θ₁ →
      used = acceptedOfClass .high hist + acceptedOfClass .low hist →
      (List.zipWith (fun q a => fare f₁ f₂ q.cls * a) I (runFrom n (ppl n θ₁) hist used I)).sum =
        f₁ * min (qtyOfClass .high I) (θ₁ - acceptedOfClass .high hist) +
        f₂ * min (qtyOfClass .low I) ((n - θ₁) - acceptedOfClass .low hist)
  | [], hist, used, hh, hl, hused => by
    simp only [runFrom, List.zipWith_nil_left, List.sum_nil, qtyOfClass_nil]
    have h1 : min 0 (θ₁ - acceptedOfClass .high hist) = 0 := min_eq_left (by linarith)
    have h2 : min 0 ((n - θ₁) - acceptedOfClass .low hist) = 0 := min_eq_left (by linarith)
    rw [h1, h2, mul_zero, mul_zero, add_zero]
  | q :: rest, hist, used, hh, hl, hused => by
    cases hcls : q.cls
    · -- q.cls = .high
      set uh := acceptedOfClass .high hist
      set ul := acceptedOfClass .low hist
      set a := min q.qty (θ₁ - uh)
      have ha0 : 0 ≤ a := le_min q.qty_pos.le (by linarith)
      have ha_le_rem : θ₁ - uh ≤ n - used := by linarith
      have hprop : max 0 (min (ppl n θ₁ hist q) (min q.qty (n - used))) = a := by
        have hp : ppl n θ₁ hist q = θ₁ - uh := by simp [ppl, hcls, uh]
        rw [hp]
        have hmin1 : min (θ₁ - uh) (min q.qty (n - used)) = a := by
          dsimp [a]
          rcases le_total q.qty (θ₁ - uh) with hq | hq
          · have hqn : q.qty ≤ n - used := by linarith
            rw [min_eq_left hqn, min_eq_right hq, min_eq_left hq]
          · rw [min_eq_right hq]
            apply min_eq_left
            exact le_min hq ha_le_rem
        rw [hmin1, max_eq_right ha0]
      simp only [runFrom, List.zipWith_cons_cons, List.sum_cons]
      rw [hprop]
      have hh' : acceptedOfClass .high (hist ++ [(q, a)]) ≤ θ₁ := by
        rw [acceptedOfClass_append, if_pos hcls]
        have : a ≤ θ₁ - uh := min_le_right _ _
        dsimp [uh] at this
        linarith
      have hl' : acceptedOfClass .low (hist ++ [(q, a)]) ≤ n - θ₁ := by
        rw [acceptedOfClass_append, if_neg (by rw [hcls]; decide), add_zero]
        exact hl
      have hused' : used + a =
          acceptedOfClass .high (hist ++ [(q, a)]) + acceptedOfClass .low (hist ++ [(q, a)]) := by
        rw [acceptedOfClass_append, acceptedOfClass_append, if_pos hcls,
          if_neg (by rw [hcls]; decide)]
        dsimp [uh, ul] at hused
        linarith
      have ih := ppl_runFrom_eq f₁ f₂ n θ₁ rest (hist ++ [(q, a)]) (used + a) hh' hl' hused'
      rw [ih, acceptedOfClass_append, acceptedOfClass_append, if_pos hcls,
        if_neg (by rw [hcls]; decide), add_zero, qtyOfClass_cons, qtyOfClass_cons,
        if_pos hcls, if_neg (by rw [hcls]; decide), zero_add]
      have hfare : fare f₁ f₂ q.cls = f₁ := by rw [hcls]; rfl
      rw [hfare]
      have hsub : θ₁ - (uh + a) = (θ₁ - uh) - a := by ring
      rw [hsub]
      have hmin_add := min_add_min_sub q.qty (qtyOfClass .high rest) (θ₁ - uh)
        (qtyOfClass_nonneg .high rest)
      have hmul := congrArg (f₁ * ·) hmin_add
      dsimp [a, uh, ul] at *
      linarith
    · -- q.cls = .low
      set uh := acceptedOfClass .high hist
      set ul := acceptedOfClass .low hist
      set a := min q.qty ((n - θ₁) - ul)
      have ha0 : 0 ≤ a := le_min q.qty_pos.le (by linarith)
      have ha_le_rem : (n - θ₁) - ul ≤ n - used := by linarith
      have hprop : max 0 (min (ppl n θ₁ hist q) (min q.qty (n - used))) = a := by
        have hp : ppl n θ₁ hist q = (n - θ₁) - ul := by simp [ppl, hcls, ul]
        rw [hp]
        have hmin1 : min ((n - θ₁) - ul) (min q.qty (n - used)) = a := by
          dsimp [a]
          rcases le_total q.qty ((n - θ₁) - ul) with hq | hq
          · have hqn : q.qty ≤ n - used := by linarith
            rw [min_eq_left hqn, min_eq_right hq, min_eq_left hq]
          · rw [min_eq_right hq]
            apply min_eq_left
            exact le_min hq ha_le_rem
        rw [hmin1, max_eq_right ha0]
      simp only [runFrom, List.zipWith_cons_cons, List.sum_cons]
      rw [hprop]
      have hh' : acceptedOfClass .high (hist ++ [(q, a)]) ≤ θ₁ := by
        rw [acceptedOfClass_append, if_neg (by rw [hcls]; decide), add_zero]
        exact hh
      have hl' : acceptedOfClass .low (hist ++ [(q, a)]) ≤ n - θ₁ := by
        rw [acceptedOfClass_append, if_pos hcls]
        have : a ≤ (n - θ₁) - ul := min_le_right _ _
        dsimp [ul] at this
        linarith
      have hused' : used + a =
          acceptedOfClass .high (hist ++ [(q, a)]) + acceptedOfClass .low (hist ++ [(q, a)]) := by
        rw [acceptedOfClass_append, acceptedOfClass_append,
          if_neg (by rw [hcls]; decide), if_pos hcls]
        dsimp [uh, ul] at hused
        linarith
      have ih := ppl_runFrom_eq f₁ f₂ n θ₁ rest (hist ++ [(q, a)]) (used + a) hh' hl' hused'
      rw [ih, acceptedOfClass_append, acceptedOfClass_append,
        if_neg (by rw [hcls]; decide), if_pos hcls, add_zero, qtyOfClass_cons, qtyOfClass_cons,
        if_neg (by rw [hcls]; decide), if_pos hcls, zero_add]
      have hfare : fare f₁ f₂ q.cls = f₂ := by rw [hcls]; rfl
      rw [hfare]
      have hsub : (n - θ₁) - (ul + a) = ((n - θ₁) - ul) - a := by ring
      rw [hsub]
      have hmin_add := min_add_min_sub q.qty (qtyOfClass .low rest) ((n - θ₁) - ul)
        (qtyOfClass_nonneg .low rest)
      have hmul := congrArg (f₂ * ·) hmin_add
      dsimp [a, uh, ul] at *
      linarith

lemma sum_class_qty (c : FareClass) :
    ∀ I : List Request,
      (∑ i : Fin I.length, if (I.get i).cls = c then (I.get i).qty else 0) = qtyOfClass c I
  | [] => by simp [qtyOfClass]
  | q :: rest => by
    change (∑ i : Fin (rest.length + 1),
      if ((q :: rest).get i).cls = c then ((q :: rest).get i).qty else 0) = qtyOfClass c (q :: rest)
    rw [Fin.sum_univ_succ, qtyOfClass_cons, ← sum_class_qty c rest]
    by_cases h : q.cls = c <;> simp [h]

lemma min_le_two_mul_min_half (Q n : ℝ) (hQ : 0 ≤ Q) :
    min Q n ≤ 2 * min Q (n / 2) := by
  rcases le_total Q (n / 2) with h | h
  · have h1 : min Q (n / 2) = Q := min_eq_left h
    have h2 : min Q n ≤ Q := min_le_left _ _
    linarith
  · have h1 : min Q (n / 2) = n / 2 := min_eq_right h
    have h2 : min Q n ≤ n := min_le_right _ _
    linarith

lemma optRevenue_le_two_mul_ppl_half (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁)
    (hn : 0 < n) (I : List Request) :
    optRevenue f₁ f₂ n I ≤ 2 * revenue f₁ f₂ n (ppl n (n / 2)) I := by
  have hf₁ : 0 < f₁ := lt_trans hf₂ hf₁₂
  have hrev : revenue f₁ f₂ n (ppl n (n / 2)) I =
      f₁ * min (qtyOfClass .high I) (n / 2) + f₂ * min (qtyOfClass .low I) (n / 2) := by
    unfold revenue accepted
    have h := ppl_runFrom_eq f₁ f₂ n (n / 2) I [] 0
      (by simp [acceptedOfClass]; linarith)
      (by simp [acceptedOfClass]; linarith)
      (by simp [acceptedOfClass])
    simp only [acceptedOfClass, List.filter_nil, List.map_nil, List.sum_nil, sub_zero] at h
    have hnh : n - n / 2 = n / 2 := by ring
    rw [hnh] at h
    exact h
  rw [hrev]
  unfold optRevenue
  apply csSup_le
  · refine ⟨0, 0, ⟨⟨fun i => ⟨le_rfl, (I.get i).qty_pos.le⟩, ?_⟩, ?_⟩⟩
    · simp [hn.le]
    · simp
  · rintro v ⟨x, ⟨hx1, hx2⟩, rfl⟩
    let xh : Fin I.length → ℝ := fun i => if (I.get i).cls = .high then x i else 0
    let xl : Fin I.length → ℝ := fun i => if (I.get i).cls = .low then x i else 0
    have hsplit : (∑ i, fare f₁ f₂ (I.get i).cls * x i) =
        f₁ * (∑ i, xh i) + f₂ * (∑ i, xl i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp [xh, xl]
      cases h : (I.get i).cls <;> simp [fare]
    have hxh_q : ∑ i, xh i ≤ qtyOfClass .high I := by
      rw [← sum_class_qty .high I]
      refine Finset.sum_le_sum fun i _ => ?_
      dsimp [xh]
      split_ifs with h
      · exact (hx1 i).2
      · exact le_rfl
    have hxl_q : ∑ i, xl i ≤ qtyOfClass .low I := by
      rw [← sum_class_qty .low I]
      refine Finset.sum_le_sum fun i _ => ?_
      dsimp [xl]
      split_ifs with h
      · exact (hx1 i).2
      · exact le_rfl
    have hxh_n : ∑ i, xh i ≤ n := by
      refine le_trans (Finset.sum_le_sum fun i _ => ?_) hx2
      dsimp [xh]
      split_ifs <;> linarith [(hx1 i).1]
    have hxl_n : ∑ i, xl i ≤ n := by
      refine le_trans (Finset.sum_le_sum fun i _ => ?_) hx2
      dsimp [xl]
      split_ifs <;> linarith [(hx1 i).1]
    have hxh_2 : ∑ i, xh i ≤ 2 * min (qtyOfClass .high I) (n / 2) :=
      le_trans (le_min hxh_q hxh_n) (min_le_two_mul_min_half _ _ (qtyOfClass_nonneg .high I))
    have hxl_2 : ∑ i, xl i ≤ 2 * min (qtyOfClass .low I) (n / 2) :=
      le_trans (le_min hxl_q hxl_n) (min_le_two_mul_min_half _ _ (qtyOfClass_nonneg .low I))
    rw [hsplit]
    nlinarith

lemma cr_ppl_le_half (f₁ f₂ n θ₁ : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n)
    (hθ0 : 0 ≤ θ₁) (hθn : θ₁ ≤ n) :
    competitiveRatio f₁ f₂ n (ppl n θ₁) ≤ 1 / 2 := by
  have hf₁ : 0 < f₁ := lt_trans hf₂ hf₁₂
  have hbdd : BddBelow {c : ℝ | ∃ I : List Request, 0 < optRevenue f₁ f₂ n I ∧
      c = revenue f₁ f₂ n (ppl n θ₁) I / optRevenue f₁ f₂ n I} := by
    refine ⟨0, ?_⟩
    rintro c ⟨I, hI, rfl⟩
    exact div_nonneg (rev_nonneg f₁ f₂ n hf₁.le hf₂.le (ppl n θ₁) I [] 0) hI.le
  unfold competitiveRatio
  have m1 := csInf_le hbdd ⟨instHigh n hn, by rw [optHigh f₁ f₂ n hf₁ hn]; positivity, rfl⟩
  have m2 := csInf_le hbdd ⟨instI2 n hn, by rw [opt2 f₁ f₂ n hf₂ hn]; positivity, rfl⟩
  rw [optHigh f₁ f₂ n hf₁ hn, rev_ppl_instHigh f₁ f₂ n θ₁ hn hθ0 hθn,
    mul_div_mul_left _ _ hf₁.ne'] at m1
  rw [opt2 f₁ f₂ n hf₂ hn, rev_ppl_instI2 f₁ f₂ n θ₁ hn hθ0 hθn,
    mul_div_mul_left _ _ hf₂.ne'] at m2
  have hsum : θ₁ / n + (n - θ₁) / n = 1 := by field_simp; ring
  linarith

end Aux_RB_ppl

open RobustBooking.TwoFare Aux_RB_ppl in
theorem solution (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n) :
    competitiveRatio f₁ f₂ n (ppl n (n / 2)) = 1 / 2 ∧
    ∀ θ₁ : ℝ, 0 ≤ θ₁ → θ₁ ≤ n → competitiveRatio f₁ f₂ n (ppl n θ₁) ≤ 1 / 2 := by
  have hf₁ : 0 < f₁ := lt_trans hf₂ hf₁₂
  refine ⟨le_antisymm (cr_ppl_le_half f₁ f₂ n (n / 2) hf₂ hf₁₂ hn (by linarith) (by linarith)) ?_,
    fun θ₁ hθ0 hθn => cr_ppl_le_half f₁ f₂ n θ₁ hf₂ hf₁₂ hn hθ0 hθn⟩
  unfold competitiveRatio
  apply le_csInf
  · refine ⟨revenue f₁ f₂ n (ppl n (n / 2)) (instI2 n hn) / optRevenue f₁ f₂ n (instI2 n hn),
      instI2 n hn, by rw [opt2 f₁ f₂ n hf₂ hn]; positivity, rfl⟩
  · rintro c ⟨I, hI, rfl⟩
    rw [le_div_iff₀ hI]
    have hopt := optRevenue_le_two_mul_ppl_half f₁ f₂ n hf₂ hf₁₂ hn I
    linarith
