-- Prove2me | solution 1 for VolDisclosure.Evidence.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:06:57.042049+00:00
-- url     : https://prove2.me/submissions/74aa2978-2759-485d-bfae-d423eaa74c3c

import Mathlib
import Definitions.Def_VolDisclosure_Evidence_Model

open VolDisclosure.Evidence

namespace VDAux

lemma basics (P : Params) (hP : P.Standing) :
    0 < P.δ ∧ 0 < P.μ ∧ 0 < P.sStar ∧ P.μ + P.sStar / (1 + P.r) = P.sStar ∧ 0 < P.vBar ∧
      P.p * P.δ + P.vBar / (1 + P.r) = P.vBar := by
  obtain ⟨hl, hlh, hp0, hp1, hr0, hr1, hL0, hL1⟩ := hP
  have hδ : 0 < P.δ := by unfold Params.δ Params.Δ; exact mul_pos hL0 (by linarith)
  have hμ : 0 < P.μ := by unfold Params.μ; nlinarith
  refine ⟨hδ, hμ, ?_, ?_, ?_, ?_⟩
  · unfold Params.sStar; exact div_pos (mul_pos (by linarith) hμ) hr0
  · unfold Params.sStar; field_simp; ring
  · unfold Params.vBar; exact div_pos (mul_pos (mul_pos (by linarith) hp0) hδ) hr0
  · unfold Params.vBar; field_simp; ring

/-- bounded class -/
def Bnd (P : Params) (q : ℝ → ℝ) : Prop := ∀ w, 0 ≤ w → 0 ≤ q w ∧ q w ≤ P.sStar

/-- expected continuation -/
noncomputable def E (P : Params) (π : ℝ) (q : ℝ → ℝ) (a : Policy) : ℝ :=
  π * (P.p * q a.wdh + (1 - P.p) * q a.wdl) + (1 - π) * (P.p * q a.wnh + (1 - P.p) * q a.wnl)

lemma objective_eq (P : Params) (π : ℝ) (q : ℝ → ℝ) (a : Policy) :
    objective P π q a = (1 - a.θ) * P.μ + (1 - a.θ) / (1 + P.r) * E P π q a := rfl

lemma E_le_add (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q1 q2 : ℝ → ℝ) (D : ℝ) (a : Policy)
    (h1 : q1 a.wdh ≤ q2 a.wdh + D) (h2 : q1 a.wdl ≤ q2 a.wdl + D)
    (h3 : q1 a.wnh ≤ q2 a.wnh + D) (h4 : q1 a.wnl ≤ q2 a.wnl + D) :
    E P π q1 a ≤ E P π q2 a + D := by
  obtain ⟨hl, hlh, hp0, hp1, hr0, hr1, hL0, hL1⟩ := hP
  unfold E
  have e1 : P.p * q1 a.wdh + (1 - P.p) * q1 a.wdl ≤ P.p * q2 a.wdh + (1 - P.p) * q2 a.wdl + D := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hp0.le, mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 1 - P.p)]
  have e2 : P.p * q1 a.wnh + (1 - P.p) * q1 a.wnl ≤ P.p * q2 a.wnh + (1 - P.p) * q2 a.wnl + D := by
    nlinarith [mul_le_mul_of_nonneg_left h3 hp0.le, mul_le_mul_of_nonneg_left h4 (by linarith : (0:ℝ) ≤ 1 - P.p)]
  nlinarith [mul_le_mul_of_nonneg_left e1 hπ0, mul_le_mul_of_nonneg_left e2 (by linarith : (0:ℝ) ≤ 1 - π)]

lemma E_bounds (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hq : Bnd P q) (a : Policy) (v : ℝ) (ha : Feasible P π v a) :
    0 ≤ E P π q a ∧ E P π q a ≤ P.sStar := by
  obtain ⟨hθ0, hθ1, _, _, _, _, hw1, hw2, hw3, hw4, _⟩ := ha
  have hp0 := hP.2.2.1
  have hp1 := hP.2.2.2.1
  obtain ⟨a1, b1⟩ := hq _ hw1
  obtain ⟨a2, b2⟩ := hq _ hw2
  obtain ⟨a3, b3⟩ := hq _ hw3
  obtain ⟨a4, b4⟩ := hq _ hw4
  have hp1' : (0:ℝ) ≤ 1 - P.p := by linarith
  have hπ1' : (0:ℝ) ≤ 1 - π := by linarith
  unfold E
  constructor
  · have : 0 ≤ P.p * q a.wdh + (1 - P.p) * q a.wdl := by positivity
    have : 0 ≤ P.p * q a.wnh + (1 - P.p) * q a.wnl := by positivity
    positivity
  · have e1 : P.p * q a.wdh + (1 - P.p) * q a.wdl ≤ P.sStar := by
      nlinarith [mul_le_mul_of_nonneg_left b1 hp0.le, mul_le_mul_of_nonneg_left b2 hp1']
    have e2 : P.p * q a.wnh + (1 - P.p) * q a.wnl ≤ P.sStar := by
      nlinarith [mul_le_mul_of_nonneg_left b3 hp0.le, mul_le_mul_of_nonneg_left b4 hp1']
    nlinarith [mul_le_mul_of_nonneg_left e1 hπ0, mul_le_mul_of_nonneg_left e2 hπ1']

lemma obj_bounds (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hq : Bnd P q) (a : Policy) (v : ℝ) (ha : Feasible P π v a) :
    0 ≤ objective P π q a ∧ objective P π q a ≤ (1 - a.θ) * P.sStar := by
  obtain ⟨hE0, hE1⟩ := E_bounds P hP π hπ0 hπ1 q hq a v ha
  obtain ⟨_, hμ, _, hss, _, _⟩ := basics P hP
  have hr0 := hP.2.2.2.2.1
  have hk : 0 ≤ 1 - a.θ := by linarith [ha.2.1]
  rw [objective_eq]
  have hR : (0:ℝ) < 1 + P.r := by linarith
  constructor
  · have : 0 ≤ (1 - a.θ) / (1 + P.r) := div_nonneg hk hR.le
    positivity
  · have : (1 - a.θ) / (1 + P.r) * E P π q a ≤ (1 - a.θ) / (1 + P.r) * P.sStar :=
      mul_le_mul_of_nonneg_left hE1 (div_nonneg hk hR.le)
    have h2 : (1 - a.θ) * P.μ + (1 - a.θ) / (1 + P.r) * P.sStar = (1 - a.θ) * P.sStar := by
      rw [show (1 - a.θ) * P.μ + (1 - a.θ) / (1 + P.r) * P.sStar
          = (1 - a.θ) * (P.μ + P.sStar / (1 + P.r)) by ring, hss]
    linarith

/-- bracket of PK is at least pδ -/
lemma pk_lower (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (a : Policy) (v : ℝ) (ha : Feasible P π v a) : (1 - a.θ) * (P.p * P.δ) ≤ v := by
  obtain ⟨hθ0, hθ1, hu1, hu2, hu3, hu4, hw1, hw2, hw3, hw4, hg, hb, hn, hpk⟩ := ha
  have hp0 := hP.2.2.1
  have hp1 := hP.2.2.2.1
  have hr0 := hP.2.2.2.2.1
  have hR : (0:ℝ) < 1 + P.r := by linarith
  set Vdh := a.udh + a.wdh / (1 + P.r)
  set Vdl := a.udl + a.wdl / (1 + P.r)
  set Vnh := a.unh + a.wnh / (1 + P.r)
  set Vnl := a.unl + a.wnl / (1 + P.r)
  have h1 : 0 ≤ Vnl := by have := div_nonneg hw4 hR.le; simp only [Vnl]; linarith
  have h2 : 0 ≤ Vdl := by have := div_nonneg hw2 hR.le; simp only [Vdl]; linarith
  have hB : P.p * P.δ ≤ π * (P.p * Vdh + (1 - P.p) * Vdl) + (1 - π) * (P.p * Vnh + (1 - P.p) * Vnl) := by
    have hp1' : (0:ℝ) ≤ 1 - P.p := by linarith
    have hπ1' : (0:ℝ) ≤ 1 - π := by linarith
    have e1 : P.p * P.δ ≤ P.p * Vdh + (1 - P.p) * Vdl := by
      nlinarith [mul_le_mul_of_nonneg_left (show P.δ ≤ Vdh by linarith) hp0.le, mul_nonneg hp1' h2]
    have e2 : P.p * P.δ ≤ P.p * Vnh + (1 - P.p) * Vnl := by
      nlinarith [mul_le_mul_of_nonneg_left (show P.δ ≤ Vnh by linarith) hp0.le, mul_nonneg hp1' h1]
    nlinarith [mul_le_mul_of_nonneg_left e1 hπ0, mul_le_mul_of_nonneg_left e2 hπ1']
  rw [hpk]
  exact mul_le_mul_of_nonneg_left hB (by linarith)

lemma feasible_nonempty (P : Params) (hP : P.Standing) (π : ℝ) (v : ℝ) (hv : 0 ≤ v) :
    ∃ a, Feasible P π v a := by
  obtain ⟨hδ, _, _, _, _, _⟩ := basics P hP
  have hp0 := hP.2.2.1
  have hpd : 0 < P.p * P.δ := mul_pos hp0 hδ
  refine ⟨⟨P.p * P.δ / (P.p * P.δ + v), P.δ + v, v, P.δ + v, v, 0, 0, 0, 0⟩, ?_⟩
  simp only [Feasible]
  have hden : 0 < P.p * P.δ + v := by linarith
  refine ⟨by positivity, ?_, by linarith, hv, by linarith, hv, le_refl _, le_refl _, le_refl _,
    le_refl _, ?_, ?_, ?_, ?_⟩
  · rw [div_le_one hden]; linarith
  · simp
  · simp
  · simp
  · simp only [zero_div, add_zero]
    field_simp
    ring

lemma bdd_img (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hq : Bnd P q) (v : ℝ) :
    BddAbove (objective P π q '' {a | Feasible P π v a}) := by
  refine ⟨P.sStar, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have := obj_bounds P hP π hπ0 hπ1 q hq a v ha
  have hs := (basics P hP).2.2.1
  nlinarith [ha.1]

lemma le_T (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hq : Bnd P q) (v : ℝ) (a : Policy) (ha : Feasible P π v a) :
    objective P π q a ≤ T P π q v :=
  le_csSup (bdd_img P hP π hπ0 hπ1 q hq v) ⟨a, ha, rfl⟩

lemma T_le_of (P : Params) (π : ℝ) (q : ℝ → ℝ) (v : ℝ) (hv : 0 ≤ v) (hP : P.Standing) (M : ℝ)
    (h : ∀ a, Feasible P π v a → objective P π q a ≤ M) : T P π q v ≤ M := by
  obtain ⟨a, ha⟩ := feasible_nonempty P hP π v hv
  apply csSup_le (Set.Nonempty.image _ ⟨a, ha⟩)
  rintro _ ⟨b, hb, rfl⟩
  exact h b hb

lemma T_bounds (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hq : Bnd P q) (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ T P π q v ∧ T P π q v ≤ P.sStar ∧ T P π q v * (P.p * P.δ) ≤ P.sStar * v := by
  obtain ⟨hδ, _, hs, _, _, _⟩ := basics P hP
  have hpd : 0 < P.p * P.δ := mul_pos hP.2.2.1 hδ
  obtain ⟨a, ha⟩ := feasible_nonempty P hP π v hv
  refine ⟨le_trans (obj_bounds P hP π hπ0 hπ1 q hq a v ha).1 (le_T P hP π hπ0 hπ1 q hq v a ha),
    T_le_of P π q v hv hP _ ?_, ?_⟩
  · intro b hb
    have := obj_bounds P hP π hπ0 hπ1 q hq b v hb
    nlinarith [hb.1]
  · have : T P π q v ≤ P.sStar * v / (P.p * P.δ) := by
      apply T_le_of P π q v hv hP
      intro b hb
      have h1 := obj_bounds P hP π hπ0 hπ1 q hq b v hb
      have h2 := pk_lower P hP π hπ0 hπ1 b v hb
      rw [le_div_iff₀ hpd]
      nlinarith
    rwa [le_div_iff₀ hpd] at this

lemma T_bnd (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hq : Bnd P q) : Bnd P (T P π q) := fun v hv =>
  ⟨(T_bounds P hP π hπ0 hπ1 q hq v hv).1, (T_bounds P hP π hπ0 hπ1 q hq v hv).2.1⟩

/-- contraction / monotonicity in q -/
lemma T_le_add (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q1 q2 : ℝ → ℝ) (hq1 : Bnd P q1) (hq2 : Bnd P q2) (D : ℝ) (hD : 0 ≤ D)
    (h : ∀ w, 0 ≤ w → q1 w ≤ q2 w + D) (v : ℝ) (hv : 0 ≤ v) :
    T P π q1 v ≤ T P π q2 v + D / (1 + P.r) := by
  apply T_le_of P π q1 v hv hP
  intro a ha
  have hle := le_T P hP π hπ0 hπ1 q2 hq2 v a ha
  obtain ⟨hθ0, hθ1, _, _, _, _, hw1, hw2, hw3, hw4, _⟩ := ha
  have hE := E_le_add P hP π hπ0 hπ1 q1 q2 D a (h _ hw1) (h _ hw2) (h _ hw3) (h _ hw4)
  have hr0 := hP.2.2.2.2.1
  have hR : (0:ℝ) < 1 + P.r := by linarith
  rw [objective_eq] at hle ⊢
  have hk : 0 ≤ (1 - a.θ) / (1 + P.r) := div_nonneg (by linarith) hR.le
  have h3 := mul_le_mul_of_nonneg_left hE hk
  have h4 : (1 - a.θ) / (1 + P.r) * D ≤ D / (1 + P.r) := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hR.le
    nlinarith
  nlinarith


lemma objective_eq' (P : Params) (π : ℝ) (q : ℝ → ℝ) (a : Policy) :
    objective P π q a = (1 - a.θ) * (P.μ + E P π q a / (1 + P.r)) := by
  rw [objective_eq]; ring

lemma T_ge_vbar (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hq : Bnd P q) (v : ℝ) (hv : P.vBar ≤ v) :
    P.μ + q P.vBar / (1 + P.r) ≤ T P π q v := by
  obtain ⟨hδ, _, _, _, hvb, hvb2⟩ := basics P hP
  have hr0 := hP.2.2.2.2.1
  have hR : (0:ℝ) < 1 + P.r := by linarith
  let a : Policy := ⟨0, v - P.vBar + P.δ, v - P.vBar, v - P.vBar + P.δ, v - P.vBar,
    P.vBar, P.vBar, P.vBar, P.vBar⟩
  have ha : Feasible P π v a := by
    simp only [Feasible, a]
    refine ⟨le_refl _, by norm_num, by linarith, by linarith, by linarith, by linarith,
      hvb.le, hvb.le, hvb.le, hvb.le, le_refl _, le_refl _, by linarith, ?_⟩
    have : P.vBar / (1 + P.r) = P.vBar - P.p * P.δ := by linarith
    rw [this]; ring
  have := le_T P hP π hπ0 hπ1 q hq v a ha
  have e : objective P π q a = P.μ + q P.vBar / (1 + P.r) := by
    simp only [objective, a]; ring
  linarith

lemma T_mono_v (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hq : Bnd P q) (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    T P π q x ≤ T P π q y := by
  apply T_le_of P π q x hx hP
  intro a ha
  have hy : 0 ≤ y := le_trans hx hxy
  by_cases hθ : a.θ = 1
  · have : objective P π q a = 0 := by rw [objective_eq', hθ]; ring
    rw [this]; exact (T_bounds P hP π hπ0 hπ1 q hq y hy).1
  · have hk : 0 < 1 - a.θ := by have := ha.2.1; exact sub_pos.2 (lt_of_le_of_ne this hθ)
    set c := (y - x) / (1 - a.θ) with hc
    have hc0 : 0 ≤ c := div_nonneg (by linarith) hk.le
    let b : Policy := ⟨a.θ, a.udh + c, a.udl + c, a.unh + c, a.unl + c, a.wdh, a.wdl, a.wnh, a.wnl⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := ha
    have hb : Feasible P π y b := by
      simp only [Feasible, b]
      refine ⟨h1, h2, by linarith, by linarith, by linarith, by linarith, h7, h8, h9, h10,
        by linarith, by linarith, by linarith, ?_⟩
      have : (1 - a.θ) * c = y - x := by rw [hc]; field_simp
      linear_combination h14 - this
    have := le_T P hP π hπ0 hπ1 q hq y b hb
    have e : objective P π q b = objective P π q a := rfl
    linarith

lemma cont_at_zero (f : ℝ → ℝ) (K L : ℝ) (hK : 0 < K) (hL : 0 < L)
    (hf : ∀ v, 0 ≤ v → 0 ≤ f v ∧ f v * K ≤ L * v) : ContinuousWithinAt f (Set.Ici 0) 0 := by
  have h0 : f 0 = 0 := by
    have := hf 0 (le_refl _); nlinarith [this.1, this.2]
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨ε * K / L, by positivity, ?_⟩
  intro x hx hd
  rw [Set.mem_Ici] at hx
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hx] at hd
  rw [h0, Real.dist_eq, sub_zero, abs_of_nonneg (hf x hx).1]
  have h := (hf x hx).2
  rw [lt_div_iff₀ hL] at hd
  have : f x * K < ε * K := by nlinarith
  exact lt_of_mul_lt_mul_right this hK.le


lemma T_scale (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hq : Bnd P q) (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    x * T P π q y ≤ y * T P π q x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have : T P π q y ≤ y * T P π q x / x := by
    apply T_le_of P π q y hy.le hP
    intro a ha
    rw [le_div_iff₀ hx]
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := ha
    let b : Policy := ⟨1 - (1 - a.θ) * x / y, a.udh, a.udl, a.unh, a.unl, a.wdh, a.wdl, a.wnh, a.wnl⟩
    have hk0 : 0 ≤ (1 - a.θ) * x / y := by
      apply div_nonneg (mul_nonneg (by linarith) hx.le) hy.le
    have hk1 : (1 - a.θ) * x / y ≤ 1 := by
      rw [div_le_one hy]; nlinarith
    have hb : Feasible P π x b := by
      refine ⟨by simp only [b]; linarith, by simp only [b]; linarith, h3, h4, h5, h6, h7, h8, h9, h10,
        h11, h12, h13, ?_⟩
      simp only [b, sub_sub_cancel]
      rw [div_mul_eq_mul_div, eq_div_iff hy.ne']
      conv_lhs => rw [h14]
      ring
    have := le_T P hP π hπ0 hπ1 q hq x b hb
    have eE : E P π q b = E P π q a := rfl
    have eθ : b.θ = 1 - (1 - a.θ) * x / y := rfl
    have e : objective P π q b = (x / y) * objective P π q a := by
      rw [objective_eq', objective_eq', eE, eθ, sub_sub_cancel]; ring
    rw [e] at this
    have : x / y * objective P π q a * y = objective P π q a * x := by field_simp
    nlinarith
  rw [le_div_iff₀ hx] at this
  linarith

lemma T_cont (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hq : Bnd P q) : ContinuousOn (T P π q) (Set.Ici 0) := by
  obtain ⟨hδ, _, hss, _, _, _⟩ := basics P hP
  intro x hx
  rw [Set.mem_Ici] at hx
  rcases eq_or_lt_of_le hx with h0 | hxpos
  · rw [← h0]
    apply cont_at_zero _ (P.p * P.δ) P.sStar (mul_pos hP.2.2.1 hδ) hss
    intro v hv
    exact ⟨(T_bounds P hP π hπ0 hπ1 q hq v hv).1, (T_bounds P hP π hπ0 hπ1 q hq v hv).2.2⟩
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨min (x / 2) (ε * x / (2 * P.sStar + 1)), by positivity, ?_⟩
    intro y hy hd
    rw [Set.mem_Ici] at hy
    rw [Real.dist_eq] at hd ⊢
    have hd1 : |y - x| < x / 2 := lt_of_lt_of_le hd (min_le_left _ _)
    have hd2 : |y - x| < ε * x / (2 * P.sStar + 1) := lt_of_lt_of_le hd (min_le_right _ _)
    have hL : 0 < 2 * P.sStar + 1 := by linarith
    rw [lt_div_iff₀ hL] at hd2
    have hyb := (T_bounds P hP π hπ0 hπ1 q hq y hy).2.1
    have hxb := (T_bounds P hP π hπ0 hπ1 q hq x hx).2.1
    have hy0 := (T_bounds P hP π hπ0 hπ1 q hq y hy).1
    have hx0 := (T_bounds P hP π hπ0 hπ1 q hq x hx).1
    rcases le_total x y with hxy | hyx
    · have m := T_mono_v P hP π hπ0 hπ1 q hq x y hx hxy
      have sc := T_scale P hP π hπ0 hπ1 q hq x y hxpos hxy
      rw [abs_of_nonneg (by linarith)]
      rw [abs_of_nonneg (by linarith)] at hd2
      -- x (Ty - Tx) ≤ (y - x) Tx ≤ (y-x) s*
      have : x * (T P π q y - T P π q x) ≤ (y - x) * P.sStar := by
        nlinarith [mul_le_mul_of_nonneg_left hxb (by linarith : (0:ℝ) ≤ y - x)]
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_left hc hxpos.le]
    · have hypos : x / 2 < y := by
        have := neg_abs_le (y - x); linarith
      have hypos' : 0 < y := by linarith
      have m := T_mono_v P hP π hπ0 hπ1 q hq y x hy hyx
      have sc := T_scale P hP π hπ0 hπ1 q hq y x hypos' hyx
      rw [abs_of_nonpos (by linarith)]
      rw [abs_of_nonpos (by linarith)] at hd2
      have : y * (T P π q x - T P π q y) ≤ (x - y) * P.sStar := by
        nlinarith [mul_le_mul_of_nonneg_left hyb (by linarith : (0:ℝ) ≤ x - y)]
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_left hc hypos'.le]

end VDAux

open VDAux in
theorem solution (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π < 1)
    (q : ℝ → ℝ) (hq : InF P q) (hq1 : ∀ v, P.vBar ≤ v → q v = P.sStar) :
    InF P (T P π q) ∧ ∀ v, P.vBar ≤ v → T P π q v = P.sStar := by
  obtain ⟨_, _, _, hid, hvb, _⟩ := basics P hP
  have hb : Bnd P q := hq.2
  refine ⟨⟨T_cont P hP π hπ0 hπ1.le q hb, T_bnd P hP π hπ0 hπ1.le q hb⟩, fun v hv => ?_⟩
  have hv0 : 0 ≤ v := le_trans hvb.le hv
  apply le_antisymm (T_bounds P hP π hπ0 hπ1.le q hb v hv0).2.1
  have := T_ge_vbar P hP π hπ0 hπ1.le q hb v hv
  rw [hq1 _ (le_refl _), hid] at this
  exact this
