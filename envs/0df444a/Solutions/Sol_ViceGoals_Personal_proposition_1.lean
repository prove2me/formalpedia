-- Prove2me | solution 1 for ViceGoals.Personal.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T06:24:43.991048+00:00
-- url     : https://prove2.me/submissions/f1154c3a-5e7a-4c41-86fb-9b833138d10f

import Mathlib
import Definitions.Def_ViceGoals_Personal_Model

set_option autoImplicit false

namespace VGP5c
open ViceGoals.Personal

/-- Abstract monopoly lemma: linear demand `A - p` truncated at the reservation price `P`. -/
lemma mono_price (D : ℝ → ℝ → Prop) (A P : ℝ) (hP : 0 < P) (hPA : P < A)
    (hfun : ∀ p Q, 0 ≤ p → D p Q → Q = if p ≤ P then A - p else 0)
    (hex : D (min (A/2) P) (A - min (A/2) P)) :
    IsMonopolyPrice D (min (A/2) P) ∧ ∀ p, IsMonopolyPrice D p → p = min (A/2) P := by
  obtain ⟨ps, hps⟩ : ∃ x, x = min (A/2) P := ⟨_, rfl⟩
  rw [← hps] at hex ⊢
  have h1 : ps ≤ A/2 := by rw [hps]; exact min_le_left _ _
  have h2 : ps ≤ P := by rw [hps]; exact min_le_right _ _
  have h3 : 0 < ps := by rw [hps]; exact lt_min (by linarith) hP
  have h4 : 0 < A - ps := by linarith
  have key : ∀ x, 0 ≤ x → x ≤ P →
      x * (A - x) ≤ ps * (A - ps) ∧ (ps * (A - ps) ≤ x * (A - x) → x = ps) := by
    intro x hx0 hxP
    rcases le_total (A/2) P with h | h
    · have e : ps = A/2 := by rw [hps]; exact min_eq_left h
      rw [e]
      refine ⟨by nlinarith [sq_nonneg (x - A/2)], fun hle => ?_⟩
      have hsq : (x - A/2)^2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
      have := (pow_eq_zero_iff two_ne_zero).1 hsq
      linarith
    · have e : ps = P := by rw [hps]; exact min_eq_right h
      rw [e]
      refine ⟨by nlinarith [mul_nonneg (sub_nonneg.2 hxP) (show 0 ≤ A - x - P by linarith)],
        fun hle => ?_⟩
      by_contra hne
      have hlt : x < P := lt_of_le_of_ne hxP hne
      nlinarith [mul_pos (sub_pos.2 hlt) (show 0 < A - x - P by linarith)]
  refine ⟨⟨h3.le, A - ps, hex, ?_⟩, ?_⟩
  · intro x Q hx hD
    rw [hfun x Q hx hD]
    split_ifs with hle
    · exact (key x hx hle).1
    · rw [mul_zero]; nlinarith [mul_pos h3 h4]
  · rintro x ⟨hx0, Q, hD, hmax⟩
    have hQ := hfun x Q hx0 hD
    have hm := hmax ps (A - ps) h3.le hex
    split_ifs at hQ with hle
    · rw [hQ] at hm; exact (key x hx0 hle).2 hm
    · rw [hQ, mul_zero] at hm; exfalso; nlinarith [mul_pos h3 h4]

lemma quad_unique (a q : ℝ) (hq : 0 ≤ q)
    (h : a * max a 0 - (max a 0)^2/2 ≤ a*q - q^2/2) : q = max a 0 := by
  rcases le_total 0 a with ha | ha
  · rw [max_eq_left ha] at h ⊢
    have hsq : (q - a)^2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
    have := (pow_eq_zero_iff two_ne_zero).1 hsq
    linarith
  · rw [max_eq_right ha] at h ⊢
    have hsq : q^2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
    exact (pow_eq_zero_iff two_ne_zero).1 hsq

lemma quad_max (a q : ℝ) (hq : 0 ≤ q) :
    a*q - q^2/2 ≤ a * max a 0 - (max a 0)^2/2 := by
  rcases le_total 0 a with ha | ha
  · rw [max_eq_left ha]; nlinarith [sq_nonneg (q - a)]
  · rw [max_eq_right ha]; nlinarith

lemma U4B_eq (m : Params) (p q : ℝ) : U4B m p q = (m.v - m.beta*m.h - p)*q - q^2/2 := by
  unfold U4B; ring

lemma U2B_eq (m : Params) (p q : ℝ) : U2B m p q = (m.v - m.h - p)*q - q^2/2 := by
  unfold U2B; ring

lemma U4_eq (m : Params) (G p q : ℝ) :
    U4 m G p q = (m.v - m.beta*m.h - p)*q - q^2/2 - penalty m G q := by
  unfold U4; rw [U4B_eq]

lemma U3_eq (m : Params) (G p q : ℝ) :
    U3 m G p q = (m.v - m.h - p)*q - q^2/2 - penalty m G q := by
  unfold U3; rw [U2B_eq]

lemma pen_nonneg (m : Params) (hlam : 0 ≤ m.lam) (G q : ℝ) : 0 ≤ penalty m G q := by
  unfold penalty; split_ifs <;> positivity

lemma pen_of_le (m : Params) {G q : ℝ} (h : q ≤ G) : penalty m G q = 0 := by
  unfold penalty; rw [if_neg (not_lt.2 h)]

lemma pen_of_lt (m : Params) {G q : ℝ} (h : G < q) : penalty m G q = m.lam * (q - G)^2 := by
  unfold penalty; rw [if_pos h]

noncomputable def qf (lam a G : ℝ) : ℝ := (a + 2*lam*G)/(1+2*lam)

noncomputable def Vf (lam a b G : ℝ) : ℝ :=
  b * qf lam a G - (qf lam a G)^2/2 - lam*(qf lam a G - G)^2

lemma qf_gt (lam a G : ℝ) (hlam : 0 < lam) (hGa : G < a) : G < qf lam a G := by
  unfold qf; rw [lt_div_iff₀ (by linarith)]; nlinarith

lemma qf_self (lam a : ℝ) (hlam : 0 < lam) : qf lam a a = a := by
  unfold qf; have : (1 + 2*lam) ≠ 0 := ne_of_gt (by linarith)
  rw [div_eq_iff this]; ring

lemma Vid (lam a b G : ℝ) (hlam : 0 < lam) :
    Vf lam a b b - Vf lam a b G = lam/(1+2*lam)*(G-b)^2 := by
  unfold Vf qf; have : (1 + 2*lam) ≠ 0 := ne_of_gt (by linarith)
  field_simp; ring

lemma optQ_corner (m : Params) (hlam : 0 ≤ m.lam) (G p a : ℝ)
    (ha : a = m.v - m.beta*m.h - p) (hG : 0 ≤ G) (haG : a ≤ G) (q : ℝ) :
    IsOptQty m G p q ↔ q = max a 0 := by
  have hU : ∀ q, U4 m G p q = a*q - q^2/2 - penalty m G q := by intro q; rw [U4_eq, ha]
  have hmaxG : max a 0 ≤ G := max_le haG hG
  have hstar : U4 m G p (max a 0) = a * max a 0 - (max a 0)^2/2 := by
    rw [hU, pen_of_le m hmaxG]; ring
  constructor
  · rintro ⟨hq0, hopt⟩
    apply quad_unique a q hq0
    have h1 := hopt (max a 0) (le_max_right _ _)
    rw [hstar, hU] at h1
    have := pen_nonneg m hlam G q
    linarith
  · rintro rfl
    refine ⟨le_max_right _ _, fun q' hq' => ?_⟩
    rw [hstar, hU]
    have := pen_nonneg m hlam G q'
    have := quad_max a q' hq'
    linarith

lemma optQ_int (m : Params) (hlam : 0 < m.lam) (G p a : ℝ)
    (ha : a = m.v - m.beta*m.h - p) (hG : 0 ≤ G) (hGa : G < a) (q : ℝ) :
    IsOptQty m G p q ↔ q = qf m.lam a G := by
  have hU : ∀ q, U4 m G p q = a*q - q^2/2 - penalty m G q := by intro q; rw [U4_eq, ha]
  obtain ⟨qG, hqG⟩ : ∃ x, x = qf m.lam a G := ⟨_, rfl⟩
  rw [← hqG]
  have ht : 0 < 1 + 2*m.lam := by linarith
  have hmul : qG * (1 + 2*m.lam) = a + 2*m.lam*G := by
    rw [hqG]; unfold qf; field_simp
  have hGq : G < qG := by rw [hqG]; exact qf_gt m.lam a G hlam hGa
  have gid : ∀ x, a*qG - qG^2/2 - m.lam*(qG-G)^2 - (a*x - x^2/2 - m.lam*(x-G)^2)
      = (1/2 + m.lam)*(x-qG)^2 := by
    intro x; linear_combination (x - qG) * hmul
  have gG : a*qG - qG^2/2 - m.lam*(qG-G)^2 - (a*G - G^2/2) = (1/2 + m.lam)*(qG-G)^2 := by
    linear_combination (G - qG) * hmul
  have hUq : U4 m G p qG = a*qG - qG^2/2 - m.lam*(qG-G)^2 := by rw [hU, pen_of_lt m hGq]
  have key : ∀ x, 0 ≤ x → U4 m G p x ≤ U4 m G p qG ∧ (U4 m G p qG ≤ U4 m G p x → x = qG) := by
    intro x hx
    rcases lt_or_ge G x with hxG | hxG
    · rw [hU x, pen_of_lt m hxG, hUq]
      have e := gid x
      have hc : 0 < 1/2 + m.lam := by linarith
      refine ⟨by nlinarith [sq_nonneg (x - qG)], fun h => ?_⟩
      have hsq : (x - qG)^2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
      have := (pow_eq_zero_iff two_ne_zero).1 hsq
      linarith
    · rw [hU x, pen_of_le m hxG, hUq]
      have hx2 : a*x - x^2/2 ≤ a*G - G^2/2 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hxG) (show 0 ≤ a - (G + x)/2 by linarith)]
      have hc : 0 < (1/2 + m.lam)*(qG-G)^2 := mul_pos (by linarith) (pow_pos (sub_pos.2 hGq) 2)
      refine ⟨by linarith, fun h => ?_⟩
      exfalso; linarith
  constructor
  · rintro ⟨hq0, hopt⟩; exact (key q hq0).2 (hopt qG (by linarith))
  · rintro rfl; exact ⟨by linarith, fun q' hq' => (key q' hq').1⟩

lemma U3_qf (m : Params) (hlam : 0 < m.lam) (G p a b : ℝ) (hb : b = m.v - m.h - p)
    (hGa : G < a) : U3 m G p (qf m.lam a G) = Vf m.lam a b G := by
  rw [U3_eq, pen_of_lt m (qf_gt m.lam a G hlam hGa), ← hb]; unfold Vf; ring

lemma goal_val (m : Params) (hlam : 0 < m.lam) (p a b : ℝ)
    (ha : a = m.v - m.beta*m.h - p) (hb : b = m.v - m.h - p) (hab : b < a) (hb0 : 0 ≤ b)
    (G q : ℝ) (hG : 0 ≤ G) (hq : IsOptQty m G p q) :
    U3 m G p q ≤ Vf m.lam a b b ∧ (Vf m.lam a b b ≤ U3 m G p q → G = b) := by
  have ht : 0 < 1 + 2*m.lam := by linarith
  rcases le_or_gt a G with haG | hGa
  · have ha0 : 0 ≤ a := by linarith
    have hqa : q = a := by
      rw [(optQ_corner m hlam.le G p a ha hG haG q).1 hq]; exact max_eq_left ha0
    rw [hqa]
    have hU : U3 m G p a = Vf m.lam a b a := by
      rw [U3_eq, pen_of_le m haG, ← hb]; unfold Vf; rw [qf_self m.lam a hlam]; ring
    have hpos : 0 < m.lam/(1+2*m.lam)*(a-b)^2 :=
      mul_pos (div_pos hlam ht) (pow_pos (sub_pos.2 hab) 2)
    have := Vid m.lam a b a hlam
    rw [hU]
    refine ⟨by linarith, fun h => ?_⟩
    exfalso; linarith
  · have hqG : q = qf m.lam a G := (optQ_int m hlam G p a ha hG hGa q).1 hq
    rw [hqG, U3_qf m hlam G p a b hb hGa]
    have e := Vid m.lam a b G hlam
    have hc : 0 < m.lam/(1+2*m.lam) := div_pos hlam ht
    have hnn : 0 ≤ m.lam/(1+2*m.lam)*(G-b)^2 := by positivity
    refine ⟨by linarith, fun h => ?_⟩
    have h0 : m.lam/(1+2*m.lam)*(G-b)^2 ≤ 0 := by linarith
    have hsq : (G - b)^2 = 0 := le_antisymm (by nlinarith [sq_nonneg (G - b)]) (sq_nonneg _)
    have := (pow_eq_zero_iff two_ne_zero).1 hsq
    linarith

lemma optGoal_b (m : Params) (hlam : 0 < m.lam) (p a b : ℝ)
    (ha : a = m.v - m.beta*m.h - p) (hb : b = m.v - m.h - p) (hab : b < a) (hb0 : 0 ≤ b) :
    IsOptGoal m p b := by
  refine ⟨hb0, qf m.lam a b, (optQ_int m hlam b p a ha hb0 hab _).2 rfl, fun G' q' hG' hq' => ?_⟩
  rw [U3_qf m hlam b p a b hb hab]
  exact (goal_val m hlam p a b ha hb hab hb0 G' q' hG' hq').1

lemma optGoal_unique (m : Params) (hlam : 0 < m.lam) (p a b : ℝ)
    (ha : a = m.v - m.beta*m.h - p) (hb : b = m.v - m.h - p) (hab : b < a) (hb0 : 0 ≤ b)
    (G : ℝ) (hG : IsOptGoal m p G) : G = b := by
  obtain ⟨hG0, q, hq, hmax⟩ := hG
  have hqb : IsOptQty m b p (qf m.lam a b) := (optQ_int m hlam b p a ha hb0 hab _).2 rfl
  have h := hmax b _ hb0 hqb
  rw [U3_qf m hlam b p a b hb hab] at h
  exact (goal_val m hlam p a b ha hb hab hb0 G q hG0 hq).2 h

noncomputable def cG (m : Params) : ℝ := m.v - m.h + (1 - m.beta)*m.h/(1+2*m.lam)

lemma Vf_nonneg_iff (m : Params) (hm : m.Standing) (p a b : ℝ)
    (ha : a = m.v - m.beta*m.h - p) (hb : b = m.v - m.h - p) (hb0 : 0 ≤ b) :
    0 ≤ Vf m.lam a b b ↔ p ≤ pbar m := by
  obtain ⟨hv, hβ0, hβ1, hh0, hlam⟩ := hm
  have ht : 0 < 1 + 2*m.lam := by linarith
  have htne : (1 + 2*m.lam) ≠ 0 := ne_of_gt ht
  have hVb : Vf m.lam a b b = (b^2 - (a-b)^2/(1+2*m.lam))/2 := by
    unfold Vf qf; field_simp; ring
  have hss : Real.sqrt (1 + 2*m.lam) ^ 2 = 1 + 2*m.lam := Real.sq_sqrt ht.le
  have hs0 : 0 < Real.sqrt (1 + 2*m.lam) := Real.sqrt_pos.2 ht
  obtain ⟨e, he⟩ : ∃ e, e = m.h * (1 - m.beta) / Real.sqrt (1 + 2 * m.lam) := ⟨_, rfl⟩
  have he0 : 0 ≤ e := by rw [he]; exact div_nonneg (mul_nonneg hh0 (by linarith)) hs0.le
  have hd : a - b = m.h * (1 - m.beta) := by rw [ha, hb]; ring
  have he2 : (a-b)^2/(1+2*m.lam) = e^2 := by rw [he, div_pow, hss, hd]
  have hpb : p ≤ pbar m ↔ e ≤ b := by
    unfold pbar; rw [← he, hb]; constructor <;> intro h <;> linarith
  rw [hpb, hVb, he2]
  constructor
  · intro hV
    by_contra hc; push Not at hc
    nlinarith [mul_self_lt_mul_self hb0 hc]
  · intro hle
    nlinarith [mul_self_le_mul_self he0 hle]

lemma demG (m : Params) (hm : m.Standing) (hh : 0 < m.h) (p Q : ℝ) (hD : IsDemandGoal m p Q) :
    Q = if p ≤ pbar m then cG m - p else 0 := by
  have hm' := hm
  obtain ⟨hv, hβ0, hβ1, hh0, hlam⟩ := hm'
  obtain ⟨G, q, hGopt, hq, rfl⟩ := hD
  obtain ⟨a, ha⟩ : ∃ x, x = m.v - m.beta*m.h - p := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ x, x = m.v - m.h - p := ⟨_, rfl⟩
  have hab : b < a := by rw [ha, hb]; nlinarith [mul_pos hh (sub_pos.2 hβ1)]
  rcases le_or_gt 0 b with hb0 | hb0
  · have hGb := optGoal_unique m hlam p a b ha hb hab hb0 G hGopt
    rw [hGb] at hq
    have hqv : q = qf m.lam a b := (optQ_int m hlam b p a ha hb0 hab q).1 hq
    rw [hGb, hqv, U3_qf m hlam b p a b hb hab]
    have hqc : qf m.lam a b = cG m - p := by
      have : (1 + 2*m.lam) ≠ 0 := ne_of_gt (by linarith)
      unfold qf cG; rw [ha, hb]; field_simp; ring
    rw [hqc]
    by_cases hp : p ≤ pbar m
    · rw [if_pos ((Vf_nonneg_iff m hm p a b ha hb hb0).2 hp), if_pos hp]
    · rw [if_neg (fun h => hp ((Vf_nonneg_iff m hm p a b ha hb hb0).1 h)), if_neg hp]
  · have hq0 : 0 ≤ q := hq.1
    have hp : ¬ p ≤ pbar m := by
      unfold pbar; intro h
      have : 0 ≤ m.h * (1 - m.beta) / Real.sqrt (1 + 2 * m.lam) :=
        div_nonneg (mul_nonneg hh0 (by linarith)) (Real.sqrt_nonneg _)
      rw [hb] at hb0; linarith
    rw [if_neg hp]
    split_ifs with hU
    · rw [U3_eq, ← hb] at hU
      have := pen_nonneg m hlam.le G q
      have hsq : q^2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
      exact (pow_eq_zero_iff two_ne_zero).1 hsq
    · rfl

lemma demG_ex (m : Params) (hm : m.Standing) (hh : 0 < m.h) (p : ℝ) (hp : p ≤ pbar m) :
    IsDemandGoal m p (cG m - p) := by
  have hm' := hm
  obtain ⟨hv, hβ0, hβ1, hh0, hlam⟩ := hm'
  obtain ⟨a, ha⟩ : ∃ x, x = m.v - m.beta*m.h - p := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ x, x = m.v - m.h - p := ⟨_, rfl⟩
  have hab : b < a := by rw [ha, hb]; nlinarith [mul_pos hh (sub_pos.2 hβ1)]
  have hb0 : 0 ≤ b := by
    have : 0 ≤ m.h * (1 - m.beta) / Real.sqrt (1 + 2 * m.lam) :=
      div_nonneg (mul_nonneg hh0 (by linarith)) (Real.sqrt_nonneg _)
    unfold pbar at hp; rw [hb]; linarith
  have hqc : qf m.lam a b = cG m - p := by
    have : (1 + 2*m.lam) ≠ 0 := ne_of_gt (by linarith)
    unfold qf cG; rw [ha, hb]; field_simp; ring
  refine ⟨b, qf m.lam a b, optGoal_b m hlam p a b ha hb hab hb0,
    (optQ_int m hlam b p a ha hb0 hab _).2 rfl, ?_⟩
  rw [U3_qf m hlam b p a b hb hab, if_pos ((Vf_nonneg_iff m hm p a b ha hb hb0).2 hp), hqc]

lemma demB (m : Params) (hm : m.Standing) (hh : 0 < m.h) (p Q : ℝ) (hD : IsDemandB m p Q) :
    Q = if p ≤ pbarB m then m.v - m.beta*m.h - p else 0 := by
  obtain ⟨hv, hβ0, hβ1, hh0, hlam⟩ := hm
  obtain ⟨q, ⟨hq0, hopt⟩, rfl⟩ := hD
  obtain ⟨a, ha⟩ : ∃ x, x = m.v - m.beta*m.h - p := ⟨_, rfl⟩
  have hq : q = max a 0 := by
    apply quad_unique a q hq0
    have := hopt (max a 0) (le_max_right _ _)
    rw [U4B_eq, U4B_eq, ← ha] at this
    exact this
  rw [U2B_eq, ← ha, hq]
  by_cases hp : p ≤ pbarB m
  · have ha0 : 0 < a := by
      unfold pbarB at hp; rw [ha]; nlinarith [mul_pos hh (sub_pos.2 hβ1)]
    rw [max_eq_left ha0.le, if_pos hp, if_pos]
    unfold pbarB at hp; rw [ha]
    nlinarith [mul_nonneg ha0.le (sub_nonneg.2 hp)]
  · rw [if_neg hp]
    push Not at hp
    rcases le_or_gt a 0 with ha0 | ha0
    · rw [max_eq_right ha0]; split_ifs <;> rfl
    · rw [max_eq_left ha0.le, if_neg]
      unfold pbarB at hp; rw [ha]; rw [ha] at ha0
      nlinarith [mul_pos ha0 (sub_pos.2 hp)]

lemma demB_ex (m : Params) (hm : m.Standing) (hh : 0 < m.h) (p : ℝ) (hp : p ≤ pbarB m) :
    IsDemandB m p (m.v - m.beta*m.h - p) := by
  obtain ⟨hv, hβ0, hβ1, hh0, hlam⟩ := hm
  have ha0 : 0 < m.v - m.beta*m.h - p := by
    unfold pbarB at hp; nlinarith [mul_pos hh (sub_pos.2 hβ1)]
  refine ⟨m.v - m.beta*m.h - p, ⟨ha0.le, fun q' hq' => ?_⟩, ?_⟩
  · rw [U4B_eq, U4B_eq]
    have := quad_max (m.v - m.beta*m.h - p) q' hq'
    rw [max_eq_left ha0.le] at this
    exact this
  · rw [if_pos]
    rw [U2B_eq]
    unfold pbarB at hp
    nlinarith [mul_nonneg ha0.le (sub_nonneg.2 hp)]

end VGP5c

open ViceGoals.Personal in
theorem solution (m : Params) (hm : m.Standing) (hh : 0 < m.h)
    (hhmax : m.h < m.v / (2 - m.beta)) :
    (∃ p, IsEqPriceB m p) ∧ (∃ p, IsEqPriceGoal m p) ∧
    ∀ pB pS : ℝ, IsEqPriceB m pB → IsEqPriceGoal m pS →
      (h1 m < m.h → pB < pS) ∧ (m.h < h1 m → pS < pB) := by
  have hm' := hm
  obtain ⟨hv, hβ0, hβ1, hh0, hlam⟩ := hm'
  have ht : 0 < 1 + 2*m.lam := by linarith
  have htne : (1 + 2*m.lam) ≠ 0 := ne_of_gt ht
  have hs1 : 1 < Real.sqrt (1 + 2*m.lam) := by
    have := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (show (1:ℝ) < 1 + 2*m.lam by linarith)
    rwa [Real.sqrt_one] at this
  have hd : 0 < m.h * (1 - m.beta) := mul_pos hh (by linarith)
  have hd' : 0 < (1 - m.beta) * m.h := mul_pos (by linarith) hh
  have hPB : 0 < pbarB m := by
    unfold pbarB
    have := (lt_div_iff₀ (by linarith : (0:ℝ) < 2 - m.beta)).1 hhmax
    linarith
  have hPBA : pbarB m < m.v - m.beta*m.h := by unfold pbarB; nlinarith
  have hPP : pbarB m < pbar m := by
    unfold pbarB pbar
    have := div_lt_self hd hs1
    nlinarith
  have hPS : 0 < pbar m := by linarith
  have hcA : VGP5c.cG m < m.v - m.beta*m.h := by
    unfold VGP5c.cG
    have := div_lt_self hd' (by linarith : (1:ℝ) < 1 + 2*m.lam)
    nlinarith
  have hPSA : pbar m < VGP5c.cG m := by
    unfold pbar VGP5c.cG
    have h1' := div_pos hd (lt_trans one_pos hs1)
    have h2' := div_pos hd' ht
    linarith
  obtain ⟨hexB, huB⟩ := VGP5c.mono_price (IsDemandB m) (m.v - m.beta*m.h) (pbarB m) hPB hPBA
    (fun p Q _ hD => VGP5c.demB m hm hh p Q hD) (VGP5c.demB_ex m hm hh _ (min_le_right _ _))
  obtain ⟨hexS, huS⟩ := VGP5c.mono_price (IsDemandGoal m) (VGP5c.cG m) (pbar m) hPS hPSA
    (fun p Q _ hD => VGP5c.demG m hm hh p Q hD) (VGP5c.demG_ex m hm hh _ (min_le_right _ _))
  refine ⟨⟨_, hexB⟩, ⟨_, hexS⟩, fun pB pS hB hS => ?_⟩
  rw [huB pB hB, huS pS hS]
  have hD : 0 < 4 - 3*m.beta + 6*m.lam - 4*m.beta*m.lam := by nlinarith
  have hkey : VGP5c.cG m - 2*pbarB m =
      (m.h*(4 - 3*m.beta + 6*m.lam - 4*m.beta*m.lam) - m.v*(1+2*m.lam))/(1+2*m.lam) := by
    unfold VGP5c.cG pbarB; field_simp; ring
  constructor
  · intro hlt
    unfold h1 at hlt
    rw [div_lt_iff₀ hD] at hlt
    have h2 : 0 < (m.h*(4 - 3*m.beta + 6*m.lam - 4*m.beta*m.lam) - m.v*(1+2*m.lam))
        /(1+2*m.lam) := div_pos (by linarith) ht
    calc min ((m.v - m.beta*m.h)/2) (pbarB m) ≤ pbarB m := min_le_right _ _
      _ < min (VGP5c.cG m/2) (pbar m) := lt_min (by linarith) hPP
  · intro hlt
    unfold h1 at hlt
    rw [lt_div_iff₀ hD] at hlt
    have h2 : (m.h*(4 - 3*m.beta + 6*m.lam - 4*m.beta*m.lam) - m.v*(1+2*m.lam))
        /(1+2*m.lam) < 0 := div_neg_of_neg_of_pos (by linarith) ht
    calc min (VGP5c.cG m/2) (pbar m) ≤ VGP5c.cG m/2 := min_le_left _ _
      _ < min ((m.v - m.beta*m.h)/2) (pbarB m) := lt_min (by linarith) (by linarith)
