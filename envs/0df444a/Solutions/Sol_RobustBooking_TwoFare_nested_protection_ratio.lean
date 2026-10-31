-- Prove2me | solution 1 for RobustBooking.TwoFare.nested_protection_ratio
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T22:26:39.97904+00:00
-- url     : https://prove2.me/submissions/c3cea55f-4759-4cac-a469-7b38d75da13b

import Mathlib
import Definitions.Def_RobustBooking_TwoFare_Booking
import Definitions.Def_RobustBooking_TwoFare_BookingPolicies
import Theorems.Thm_RobustBooking_TwoFare_randomized_upper_bound

namespace Aux_RB_nested

open RobustBooking.TwoFare MeasureTheory

lemma b_pos_and_le_one (f₁ f₂ : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) :
    0 < b (f₂ / f₁) ∧ b (f₂ / f₁) ≤ 1 ∧ (2 - f₂ / f₁) * b (f₂ / f₁) = 1 := by
  have hf₁ : 0 < f₁ := lt_trans hf₂ hf₁₂
  have hr_lt : f₂ / f₁ < 1 := (div_lt_one hf₁).mpr hf₁₂
  have hr_pos : 0 < f₂ / f₁ := div_pos hf₂ hf₁
  have hden : 1 < 2 - f₂ / f₁ := by linarith
  have hden_pos : 0 < 2 - f₂ / f₁ := by linarith
  unfold b
  refine ⟨one_div_pos.mpr hden_pos, ?_, ?_⟩
  · rw [div_le_one hden_pos]
    linarith
  · exact mul_one_div_cancel (ne_of_gt hden_pos)

lemma det_upper_bound (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n)
    (A : DetPolicy) :
    competitiveRatio f₁ f₂ n A ≤ b (f₂ / f₁) := by
  let μ : Measure Unit := Measure.dirac ()
  have hprob : IsProbabilityMeasure μ := Measure.dirac.isProbabilityMeasure
  have h1 := (randomized_upper_bound f₁ f₂ n hf₂ hf₁₂ hn μ (fun _ => A)
    (fun _ => measurable_const)).1
  have heq : competitiveRatio f₁ f₂ n A = randCompetitiveRatio f₁ f₂ n μ (fun _ => A) := by
    unfold competitiveRatio randCompetitiveRatio
    congr 1
    ext c
    simp [μ]
  rw [heq]
  exact h1

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

lemma acceptedOfClass_append (c : FareClass) (hist : List (Request × ℝ)) (q : Request) (a : ℝ) :
    acceptedOfClass c (hist ++ [(q, a)]) =
      acceptedOfClass c hist + (if q.cls = c then a else 0) := by
  unfold acceptedOfClass
  rw [List.filter_append, List.map_append, List.sum_append]
  by_cases h : q.cls = c <;> simp [h]

noncomputable def runAcceptedClass (c : FareClass) (n : ℝ) (A : DetPolicy) :
    List (Request × ℝ) → ℝ → List Request → ℝ
  | _, _, [] => 0
  | hist, used, q :: rest =>
    let prop := A hist q
    let a := max 0 (min prop (min q.qty (n - used)))
    (if q.cls = c then a else 0) + runAcceptedClass c n A (hist ++ [(q, a)]) (used + a) rest

lemma runFrom_rev_eq_classes (f₁ f₂ n : ℝ) (A : DetPolicy) :
    ∀ (I : List Request) (hist : List (Request × ℝ)) (used : ℝ),
      (List.zipWith (fun q a => fare f₁ f₂ q.cls * a) I (runFrom n A hist used I)).sum =
        f₁ * runAcceptedClass .high n A hist used I +
        f₂ * runAcceptedClass .low n A hist used I
  | [], hist, used => by simp [runFrom, runAcceptedClass]
  | q :: rest, hist, used => by
    simp only [runFrom, runAcceptedClass, List.zipWith_cons_cons, List.sum_cons]
    rw [runFrom_rev_eq_classes f₁ f₂ n A rest]
    cases q.cls <;> simp [fare] <;> ring

lemma runAcceptedClass_nonneg (c : FareClass) (n : ℝ) (A : DetPolicy) :
    ∀ (I : List Request) (hist : List (Request × ℝ)) (used : ℝ),
      0 ≤ runAcceptedClass c n A hist used I
  | [], _, _ => le_rfl
  | q :: rest, hist, used => by
    simp only [runAcceptedClass]
    refine add_nonneg ?_ (runAcceptedClass_nonneg c n A rest _ _)
    split_ifs
    · exact le_max_left 0 _
    · exact le_rfl

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

lemma nested_invariants (n θ₁ : ℝ) :
    ∀ (I : List Request) (hist : List (Request × ℝ)) (used : ℝ),
      acceptedOfClass .low hist ≤ n - θ₁ →
      used ≤ n →
      runAcceptedClass .low n (nested n θ₁) hist used I ≤ (n - θ₁) - acceptedOfClass .low hist ∧
      used + runAcceptedClass .high n (nested n θ₁) hist used I +
        runAcceptedClass .low n (nested n θ₁) hist used I ≤ n ∧
      (used + runAcceptedClass .high n (nested n θ₁) hist used I +
          runAcceptedClass .low n (nested n θ₁) hist used I = n ∨
        (runAcceptedClass .high n (nested n θ₁) hist used I = qtyOfClass .high I ∧
         runAcceptedClass .low n (nested n θ₁) hist used I =
           min (qtyOfClass .low I) ((n - θ₁) - acceptedOfClass .low hist)))
  | [], hist, used, hl, hused => by
    simp only [runAcceptedClass, qtyOfClass_nil, add_zero]
    have hmin : min 0 ((n - θ₁) - acceptedOfClass .low hist) = 0 := min_eq_left (by linarith)
    exact ⟨by linarith, hused, Or.inr ⟨trivial, hmin.symm⟩⟩
  | q :: rest, hist, used, hl, hused => by
    set prop := nested n θ₁ hist q
    set a := max 0 (min prop (min q.qty (n - used)))
    have ha_nonneg : 0 ≤ a := le_max_left 0 _
    have ha_le_rem : a ≤ n - used := by
      dsimp [a]
      exact max_le (by linarith) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hused' : used + a ≤ n := by linarith
    have hl' : acceptedOfClass .low (hist ++ [(q, a)]) ≤ n - θ₁ := by
      rw [acceptedOfClass_append]
      split_ifs with hcls
      · have hprop : prop = (n - θ₁) - acceptedOfClass .low hist := by simp [prop, nested, hcls]
        have ha_le_prop : a ≤ prop := by
          dsimp [a]
          exact max_le (by rw [hprop]; linarith) (min_le_left _ _)
        linarith
      · linarith
    obtain ⟨ih1, ih2, ih3⟩ := nested_invariants n θ₁ rest (hist ++ [(q, a)]) (used + a) hl' hused'
    simp only [runAcceptedClass]
    have hsum_step :
        used + ((if q.cls = .high then a else 0) +
          runAcceptedClass .high n (nested n θ₁) (hist ++ [(q, a)]) (used + a) rest) +
        ((if q.cls = .low then a else 0) +
          runAcceptedClass .low n (nested n θ₁) (hist ++ [(q, a)]) (used + a) rest) =
        (used + a) + runAcceptedClass .high n (nested n θ₁) (hist ++ [(q, a)]) (used + a) rest +
          runAcceptedClass .low n (nested n θ₁) (hist ++ [(q, a)]) (used + a) rest := by
      cases q.cls <;> simp <;> ring
    refine ⟨?_, ?_, ?_⟩
    · rw [acceptedOfClass_append] at ih1
      split_ifs with hcls
      · rw [if_pos hcls] at ih1
        dsimp [a, prop] at ih1 ⊢
        linarith
      · rw [if_neg hcls] at ih1
        dsimp [a, prop] at ih1 ⊢
        linarith
    · linarith
    · rcases ih3 with hfull | ⟨ih_high, ih_low⟩
      · left
        linarith
      · by_cases hfull2 :
            (used + a) + runAcceptedClass .high n (nested n θ₁) (hist ++ [(q, a)]) (used + a) rest +
              runAcceptedClass .low n (nested n θ₁) (hist ++ [(q, a)]) (used + a) rest = n
        · left
          linarith
        · right
          have hlt_n : (used + a) +
              runAcceptedClass .high n (nested n θ₁) (hist ++ [(q, a)]) (used + a) rest +
              runAcceptedClass .low n (nested n θ₁) (hist ++ [(q, a)]) (used + a) rest < n :=
            lt_of_le_of_ne ih2 hfull2
          have h_rh_nonneg := runAcceptedClass_nonneg .high n (nested n θ₁) rest (hist ++ [(q, a)]) (used + a)
          have h_rl_nonneg := runAcceptedClass_nonneg .low n (nested n θ₁) rest (hist ++ [(q, a)]) (used + a)
          have ha_lt_rem : a < n - used := by linarith
          cases hcls : q.cls
          · -- q.cls = .high
            have hprop : prop = q.qty := by simp [prop, nested, hcls]
            have ha_eq : a = q.qty := by
              have h1 : a = min q.qty (n - used) := by
                dsimp [a]
                rw [hprop, min_eq_right (min_le_left _ _), max_eq_right (le_min q.qty_pos.le (by linarith))]
              rcases le_total q.qty (n - used) with hle | hle
              · rw [h1, min_eq_left hle]
              · rw [h1, min_eq_right hle] at ha_lt_rem
                exact False.elim (lt_irrefl _ ha_lt_rem)
            rw [qtyOfClass_cons, qtyOfClass_cons]
            simp only [hcls, ↓reduceIte]
            dsimp [a, prop] at ih_high ih_low ha_eq ⊢
            rw [zero_add, zero_add, ih_high, ih_low,
              acceptedOfClass_append, if_neg (by rw [hcls]; decide), add_zero, ha_eq]
            exact ⟨rfl, rfl⟩
          · -- q.cls = .low
            have hprop : prop = (n - θ₁) - acceptedOfClass .low hist := by simp [prop, nested, hcls]
            have ha_eq : a = min q.qty ((n - θ₁) - acceptedOfClass .low hist) := by
              have h0 : 0 ≤ min prop (min q.qty (n - used)) :=
                le_min (by rw [hprop]; linarith) (le_min q.qty_pos.le (by linarith))
              have h1 : a = min prop (min q.qty (n - used)) := max_eq_right h0
              rcases le_total (min prop q.qty) (n - used) with hle | hle
              · rw [h1, ← min_assoc, min_eq_left hle, hprop, min_comm]
              · rw [h1, ← min_assoc, min_eq_right hle] at ha_lt_rem
                exact False.elim (lt_irrefl _ ha_lt_rem)
            rw [qtyOfClass_cons, qtyOfClass_cons]
            simp only [hcls, ↓reduceIte]
            dsimp [a, prop] at ih_high ih_low ha_eq ⊢
            rw [zero_add, zero_add, ih_high, ih_low,
              acceptedOfClass_append, if_pos hcls]
            refine ⟨rfl, ?_⟩
            set a0 := max 0 (min (nested n θ₁ hist q) (min q.qty (n - used)))
            have hsub : (n - θ₁) - (acceptedOfClass .low hist + a0) =
                ((n - θ₁) - acceptedOfClass .low hist) - a0 := by ring
            rw [hsub, ha_eq]
            exact min_add_min_sub q.qty (qtyOfClass .low rest)
              ((n - θ₁) - acceptedOfClass .low hist) (qtyOfClass_nonneg .low rest)

lemma sum_class_qty (c : FareClass) :
    ∀ I : List Request,
      (∑ i : Fin I.length, if (I.get i).cls = c then (I.get i).qty else 0) = qtyOfClass c I
  | [] => by simp [qtyOfClass]
  | q :: rest => by
    change (∑ i : Fin (rest.length + 1),
      if ((q :: rest).get i).cls = c then ((q :: rest).get i).qty else 0) = qtyOfClass c (q :: rest)
    rw [Fin.sum_univ_succ, qtyOfClass_cons, ← sum_class_qty c rest]
    by_cases h : q.cls = c <;> simp [h]

lemma optRevenue_le_fn (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n)
    (I : List Request) :
    optRevenue f₁ f₂ n I ≤ f₁ * n := by
  have hf₁ : 0 < f₁ := lt_trans hf₂ hf₁₂
  unfold optRevenue
  apply csSup_le
  · refine ⟨0, 0, ⟨⟨fun i => ⟨le_rfl, (I.get i).qty_pos.le⟩, ?_⟩, ?_⟩⟩
    · simp [hn.le]
    · simp
  · rintro v ⟨x, ⟨hx1, hx2⟩, rfl⟩
    calc ∑ i, fare f₁ f₂ (I.get i).cls * x i
        ≤ ∑ i, f₁ * x i := by
          refine Finset.sum_le_sum fun i _ => ?_
          apply mul_le_mul_of_nonneg_right _ (hx1 i).1
          cases (I.get i).cls <;> (simp [fare]; try linarith)
      _ = f₁ * ∑ i, x i := (Finset.mul_sum _ _ _).symm
      _ ≤ f₁ * n := mul_le_mul_of_nonneg_left hx2 hf₁.le

lemma optRevenue_le_split (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n)
    (I : List Request) :
    optRevenue f₁ f₂ n I ≤ f₁ * qtyOfClass .high I + f₂ * min (qtyOfClass .low I) n := by
  have hf₁ : 0 < f₁ := lt_trans hf₂ hf₁₂
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
      cases (I.get i).cls <;> simp [fare]
    have hxh_qty : (∑ i, xh i) ≤ qtyOfClass .high I := by
      rw [← sum_class_qty .high I]
      refine Finset.sum_le_sum fun i _ => ?_
      dsimp [xh]
      split_ifs <;> [exact (hx1 i).2; exact le_rfl]
    have hxl_qty : (∑ i, xl i) ≤ qtyOfClass .low I := by
      rw [← sum_class_qty .low I]
      refine Finset.sum_le_sum fun i _ => ?_
      dsimp [xl]
      split_ifs <;> [exact (hx1 i).2; exact le_rfl]
    have hxl_n : (∑ i, xl i) ≤ n := by
      refine le_trans (Finset.sum_le_sum fun i _ => ?_) hx2
      dsimp [xl]
      split_ifs <;> [exact le_rfl; exact (hx1 i).1]
    have hxl_min : (∑ i, xl i) ≤ min (qtyOfClass .low I) n := le_min hxl_qty hxl_n
    rw [hsplit]
    nlinarith

end Aux_RB_nested

namespace RobustBooking.TwoFare

open Aux_RB_nested

theorem nested_protection_ratio (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n) :
    competitiveRatio f₁ f₂ n (nested n ((1 - b (f₂ / f₁)) * n)) = b (f₂ / f₁) := by
  have hf₁ : 0 < f₁ := lt_trans hf₂ hf₁₂
  obtain ⟨hb_pos, hb_le_one, hb_eq⟩ := b_pos_and_le_one f₁ f₂ hf₂ hf₁₂
  set θ₁ := (1 - b (f₂ / f₁)) * n
  have hB : n - θ₁ = b (f₂ / f₁) * n := by dsimp [θ₁]; ring
  apply le_antisymm
  · exact det_upper_bound f₁ f₂ n hf₂ hf₁₂ hn (nested n θ₁)
  · unfold competitiveRatio
    apply le_csInf
    · refine ⟨_, instI2 n hn, ?_, rfl⟩
      rw [opt2 f₁ f₂ n hf₂ hn]
      exact mul_pos hf₂ hn
    · rintro c ⟨I, hI, rfl⟩
      rw [le_div_iff₀ hI]
      have hopt_fn := optRevenue_le_fn f₁ f₂ n hf₂ hf₁₂ hn I
      have hopt_split := optRevenue_le_split f₁ f₂ n hf₂ hf₁₂ hn I
      have hl0 : acceptedOfClass .low [] ≤ n - θ₁ := by
        simp only [acceptedOfClass, List.filter_nil, List.map_nil, List.sum_nil]
        rw [hB]
        exact mul_nonneg hb_pos.le hn.le
      obtain ⟨inv1, inv2, inv3⟩ := nested_invariants n θ₁ I [] 0 hl0 hn.le
      simp only [acceptedOfClass, List.filter_nil, List.map_nil, List.sum_nil, sub_zero, zero_add]
        at inv1 inv2 inv3
      have hrev : revenue f₁ f₂ n (nested n θ₁) I =
          f₁ * runAcceptedClass .high n (nested n θ₁) [] 0 I +
          f₂ * runAcceptedClass .low n (nested n θ₁) [] 0 I := by
        unfold revenue accepted
        exact runFrom_rev_eq_classes f₁ f₂ n (nested n θ₁) I [] 0
      rw [hrev]
      set AH := runAcceptedClass .high n (nested n θ₁) [] 0 I
      set AL := runAcceptedClass .low n (nested n θ₁) [] 0 I
      rcases inv3 with hfull | ⟨hAH, hAL⟩
      · -- Case 1: AH + AL = n and AL ≤ b(r) * n
        rw [hB] at inv1
        have hAH_eq : AH = n - AL := by dsimp [AH, AL] at hfull ⊢; linarith
        have h_id : f₁ * n - (f₁ - f₂) * (b (f₂ / f₁) * n) = b (f₂ / f₁) * (f₁ * n) := by
          have h1 : f₂ = (f₂ / f₁) * f₁ := (div_mul_cancel₀ f₂ hf₁.ne').symm
          have h2 : f₁ * n - (f₁ - f₂) * (b (f₂ / f₁) * n) =
              f₁ * n * (1 - (1 - f₂ / f₁) * b (f₂ / f₁)) := by
            calc f₁ * n - (f₁ - f₂) * (b (f₂ / f₁) * n)
                = f₁ * n - (f₁ - f₂ / f₁ * f₁) * (b (f₂ / f₁) * n) := by rw [← h1]
              _ = f₁ * n * (1 - (1 - f₂ / f₁) * b (f₂ / f₁)) := by ring
          have h3 : 1 - (1 - f₂ / f₁) * b (f₂ / f₁) = b (f₂ / f₁) := by
            linarith [hb_eq]
          rw [h2, h3]
          ring
        dsimp [AH, AL] at *
        nlinarith [hopt_fn, inv1, h_id]
      · -- Case 2: AH = qtyOfClass .high I and AL = min (qtyOfClass .low I) (b(r) * n)
        rw [hB] at hAL
        have h_min_scale : b (f₂ / f₁) * min (qtyOfClass .low I) n ≤
            min (qtyOfClass .low I) (b (f₂ / f₁) * n) := by
          refine le_min ?_ ?_
          · calc b (f₂ / f₁) * min (qtyOfClass .low I) n
                ≤ 1 * min (qtyOfClass .low I) n :=
                  mul_le_mul_of_nonneg_right hb_le_one (le_min (qtyOfClass_nonneg .low I) hn.le)
              _ = min (qtyOfClass .low I) n := one_mul _
              _ ≤ qtyOfClass .low I := min_le_left _ _
          · exact mul_le_mul_of_nonneg_left (min_le_right _ _) hb_pos.le
        have h_high_scale : b (f₂ / f₁) * qtyOfClass .high I ≤ qtyOfClass .high I := by
          calc b (f₂ / f₁) * qtyOfClass .high I
              ≤ 1 * qtyOfClass .high I :=
                mul_le_mul_of_nonneg_right hb_le_one (qtyOfClass_nonneg .high I)
            _ = qtyOfClass .high I := one_mul _
        dsimp [AH, AL] at *
        rw [hAH, hAL]
        nlinarith [hopt_split, h_min_scale, h_high_scale]

end RobustBooking.TwoFare

theorem solution (f₁ f₂ n : ℝ) (hf₂ : 0 < f₂) (hf₁₂ : f₂ < f₁) (hn : 0 < n) :
    RobustBooking.TwoFare.competitiveRatio f₁ f₂ n
      (RobustBooking.TwoFare.nested n ((1 - RobustBooking.TwoFare.b (f₂ / f₁)) * n)) =
    RobustBooking.TwoFare.b (f₂ / f₁) :=
  RobustBooking.TwoFare.nested_protection_ratio f₁ f₂ n hf₂ hf₁₂ hn
