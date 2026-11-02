-- Prove2me | solution 1 for VolDisclosure.Evidence.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:10:24.647499+00:00
-- url     : https://prove2.me/submissions/c89a120e-27fb-4cf2-8576-93ab2a8ab2d3

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

/-- PK bracket -/
noncomputable def Bk (P : Params) (π : ℝ) (a : Policy) : ℝ :=
  π * (P.p * (a.udh + a.wdh / (1 + P.r)) + (1 - P.p) * (a.udl + a.wdl / (1 + P.r)))
      + (1 - π) * (P.p * (a.unh + a.wnh / (1 + P.r)) + (1 - P.p) * (a.unl + a.wnl / (1 + P.r)))

/-- mixture policy -/
def mixPol (α γ k : ℝ) (a1 a2 : Policy) : Policy :=
  ⟨1 - k, α * a1.udh + γ * a2.udh, α * a1.udl + γ * a2.udl,
      α * a1.unh + γ * a2.unh, α * a1.unl + γ * a2.unl, α * a1.wdh + γ * a2.wdh,
      α * a1.wdl + γ * a2.wdl, α * a1.wnh + γ * a2.wnh, α * a1.wnl + γ * a2.wnl⟩

lemma Bk_mix (P : Params) (π α γ k : ℝ) (a1 a2 : Policy) :
    Bk P π (mixPol α γ k a1 a2) = α * Bk P π a1 + γ * Bk P π a2 := by
  simp only [Bk, mixPol]; ring

lemma comb (α γ f1 g1 f2 g2 : ℝ) (hα0 : 0 ≤ α) (hγ0 : 0 ≤ γ) (h1 : g1 ≤ f1) (h2 : g2 ≤ f2) :
    α * g1 + γ * g2 ≤ α * f1 + γ * f2 := by
  nlinarith [mul_le_mul_of_nonneg_left h1 hα0, mul_le_mul_of_nonneg_left h2 hγ0]

lemma V_mix (r α γ u1 u2 w1 w2 : ℝ) : α * u1 + γ * u2 + (α * w1 + γ * w2) / (1 + r)
    = α * (u1 + w1 / (1 + r)) + γ * (u2 + w2 / (1 + r)) := by ring

lemma mix_feas (P : Params) (π α γ k x y : ℝ) (hα0 : 0 ≤ α) (hγ0 : 0 ≤ γ) (hαγ : α + γ = 1)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (a1 a2 : Policy)
    (ha1 : Feasible P π x a1) (ha2 : Feasible P π y a2) :
    Feasible P π (k * (α * Bk P π a1 + γ * Bk P π a2)) (mixPol α γ k a1 a2) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14⟩ := ha1
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := ha2
  refine ⟨by simp only [mixPol]; linarith, by simp only [mixPol]; linarith,
    by simp only [mixPol]; positivity, by simp only [mixPol]; positivity,
    by simp only [mixPol]; positivity, by simp only [mixPol]; positivity,
    by simp only [mixPol]; positivity, by simp only [mixPol]; positivity,
    by simp only [mixPol]; positivity, by simp only [mixPol]; positivity, ?_, ?_, ?_, ?_⟩
  · simp only [mixPol]; rw [V_mix, V_mix]; exact comb _ _ _ _ _ _ hα0 hγ0 b11 c11
  · simp only [mixPol]; rw [V_mix, V_mix]; exact comb _ _ _ _ _ _ hα0 hγ0 b12 c12
  · simp only [mixPol]; rw [V_mix]
    have := comb _ _ _ _ _ _ hα0 hγ0 b13 c13
    have e3 := V_mix P.r α γ a1.unl a2.unl a1.wnl a2.wnl
    have e2 : α * (P.δ + a1.unl + a1.wnl / (1 + P.r)) + γ * (P.δ + a2.unl + a2.wnl / (1 + P.r))
        = P.δ + (α * (a1.unl + a1.wnl / (1 + P.r)) + γ * (a2.unl + a2.wnl / (1 + P.r))) := by
      linear_combination P.δ * hαγ
    rw [e2] at this
    linarith
  · have := Bk_mix P π α γ k a1 a2
    unfold Bk at this
    rw [this]
    simp only [mixPol, sub_sub_cancel]
    rfl

lemma E_mix (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hc : ConcaveOn ℝ (Set.Ici 0) q) (α γ k x y : ℝ) (hα0 : 0 ≤ α) (hγ0 : 0 ≤ γ)
    (hαγ : α + γ = 1) (a1 a2 : Policy)
    (ha1 : Feasible P π x a1) (ha2 : Feasible P π y a2) :
    α * E P π q a1 + γ * E P π q a2 ≤ E P π q (mixPol α γ k a1 a2) := by
  have cq : ∀ w1 w2 : ℝ, 0 ≤ w1 → 0 ≤ w2 → α * q w1 + γ * q w2 ≤ q (α * w1 + γ * w2) := by
    intro w1 w2 h1 h2
    have := hc.2 (Set.mem_Ici.2 h1) (Set.mem_Ici.2 h2) hα0 hγ0 hαγ
    simpa [smul_eq_mul] using this
  obtain ⟨_, _, _, _, _, _, b7, b8, b9, b10, _⟩ := ha1
  obtain ⟨_, _, _, _, _, _, c7, c8, c9, c10, _⟩ := ha2
  have d1 := cq _ _ b7 c7
  have d2 := cq _ _ b8 c8
  have d3 := cq _ _ b9 c9
  have d4 := cq _ _ b10 c10
  have hp0 := hP.2.2.1
  have hp1 : 0 ≤ 1 - P.p := by linarith [hP.2.2.2.1]
  have hπ1' : 0 ≤ 1 - π := by linarith
  clear cq
  simp only [E, mixPol]
  linarith [mul_le_mul_of_nonneg_left d1 (mul_nonneg hπ0 hp0.le),
    mul_le_mul_of_nonneg_left d2 (mul_nonneg hπ0 hp1),
    mul_le_mul_of_nonneg_left d3 (mul_nonneg hπ1' hp0.le),
    mul_le_mul_of_nonneg_left d4 (mul_nonneg hπ1' hp1)]

lemma pk_eq (P : Params) (π v : ℝ) (a : Policy) (ha : Feasible P π v a) :
    v = (1 - a.θ) * Bk P π a := ha.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- mixing two feasible policies -/
lemma mix_le (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hq : Bnd P q) (hc : ConcaveOn ℝ (Set.Ici 0) q)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (t1 t2 : ℝ) (ht1 : 0 ≤ t1) (ht2 : 0 ≤ t2) (ht : t1 + t2 = 1)
    (a1 a2 : Policy) (ha1 : Feasible P π x a1) (ha2 : Feasible P π y a2) :
    t1 * objective P π q a1 + t2 * objective P π q a2 ≤ T P π q (t1 * x + t2 * y) := by
  have hz : 0 ≤ t1 * x + t2 * y := by positivity
  have hr0 := hP.2.2.2.2.1
  have hR : (0:ℝ) < 1 + P.r := by linarith
  have hk10 : 0 ≤ 1 - a1.θ := by linarith [ha1.2.1]
  have hk20 : 0 ≤ 1 - a2.θ := by linarith [ha2.2.1]
  have hk11 : 1 - a1.θ ≤ 1 := by linarith [ha1.1]
  have hk21 : 1 - a2.θ ≤ 1 := by linarith [ha2.1]
  have hx' := pk_eq P π x a1 ha1
  have hy' := pk_eq P π y a2 ha2
  rw [objective_eq', objective_eq']
  generalize 1 - a1.θ = k1 at *
  generalize 1 - a2.θ = k2 at *
  have hT0 := (T_bounds P hP π hπ0 hπ1 q hq _ hz).1
  rcases eq_or_lt_of_le (show 0 ≤ t1 * k1 + t2 * k2 by positivity) with hk0 | hkpos
  · have e1 : t1 * k1 = 0 := by nlinarith [mul_nonneg ht1 hk10, mul_nonneg ht2 hk20]
    have e2 : t2 * k2 = 0 := by nlinarith [mul_nonneg ht1 hk10, mul_nonneg ht2 hk20]
    have : t1 * (k1 * (P.μ + E P π q a1 / (1 + P.r))) + t2 * (k2 * (P.μ + E P π q a2 / (1 + P.r)))
        = 0 := by rw [← mul_assoc, ← mul_assoc, e1, e2]; ring
    rw [this]; exact hT0
  · generalize hk : t1 * k1 + t2 * k2 = k at *
    have hk1' : k ≤ 1 := by
      rw [← hk]; nlinarith [mul_le_mul_of_nonneg_left hk11 ht1, mul_le_mul_of_nonneg_left hk21 ht2]
    have hα0 : 0 ≤ t1 * k1 / k := by positivity
    have hγ0 : 0 ≤ t2 * k2 / k := by positivity
    have hαγ : t1 * k1 / k + t2 * k2 / k = 1 := by
      rw [← add_div, hk, div_self hkpos.ne']
    have hkα : k * (t1 * k1 / k) = t1 * k1 := mul_div_cancel₀ _ hkpos.ne'
    have hkγ : k * (t2 * k2 / k) = t2 * k2 := mul_div_cancel₀ _ hkpos.ne'
    generalize t1 * k1 / k = α at *
    generalize t2 * k2 / k = γ at *
    have hfe := mix_feas P π α γ k x y hα0 hγ0 hαγ hkpos.le hk1' a1 a2 ha1 ha2
    have hv : k * (α * Bk P π a1 + γ * Bk P π a2) = t1 * x + t2 * y := by
      rw [hx', hy']; linear_combination (Bk P π a1) * hkα + (Bk P π a2) * hkγ
    rw [hv] at hfe
    have hT := le_T P hP π hπ0 hπ1 q hq _ _ hfe
    have hE := E_mix P hP π hπ0 hπ1 q hc α γ k x y hα0 hγ0 hαγ a1 a2 ha1 ha2
    have hθ : (mixPol α γ k a1 a2).θ = 1 - k := rfl
    rw [objective_eq', hθ, sub_sub_cancel] at hT
    have hE' : k * (α * E P π q a1 + γ * E P π q a2) ≤ k * E P π q (mixPol α γ k a1 a2) :=
      mul_le_mul_of_nonneg_left hE hkpos.le
    have key : t1 * (k1 * (P.μ + E P π q a1 / (1 + P.r))) + t2 * (k2 * (P.μ + E P π q a2 / (1 + P.r)))
        = k * P.μ + (k * (α * E P π q a1 + γ * E P π q a2)) / (1 + P.r) := by
      linear_combination P.μ * hk - (E P π q a1 / (1 + P.r)) * hkα - (E P π q a2 / (1 + P.r)) * hkγ
    have h3 : (k * (α * E P π q a1 + γ * E P π q a2)) / (1 + P.r)
        ≤ k * E P π q (mixPol α γ k a1 a2) / (1 + P.r) :=
      div_le_div_of_nonneg_right hE' hR.le
    have h4 : k * (P.μ + E P π q (mixPol α γ k a1 a2) / (1 + P.r))
        = k * P.μ + k * E P π q (mixPol α γ k a1 a2) / (1 + P.r) := by ring
    rw [key]
    exact le_trans (by linarith) hT


lemma T_concave (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (q : ℝ → ℝ) (hq : Bnd P q) (hc : ConcaveOn ℝ (Set.Ici 0) q) :
    ConcaveOn ℝ (Set.Ici 0) (T P π q) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy t1 t2 ht1 ht2 ht
  simp only [smul_eq_mul]
  rw [Set.mem_Ici] at hx hy
  have step1 : ∀ a2, Feasible P π y a2 →
      t1 * T P π q x + t2 * objective P π q a2 ≤ T P π q (t1 * x + t2 * y) := by
    intro a2 ha2
    rcases eq_or_lt_of_le ht1 with h0 | hpos
    · obtain ⟨a1, ha1⟩ := feasible_nonempty P hP π x hx
      have := mix_le P hP π hπ0 hπ1 q hq hc x y hx hy t1 t2 ht1 ht2 ht a1 a2 ha1 ha2
      rw [← h0] at this ⊢; simpa using this
    · have : T P π q x ≤ (T P π q (t1 * x + t2 * y) - t2 * objective P π q a2) / t1 := by
        apply T_le_of P π q x hx hP
        intro a1 ha1; rw [le_div_iff₀ hpos]
        have := mix_le P hP π hπ0 hπ1 q hq hc x y hx hy t1 t2 ht1 ht2 ht a1 a2 ha1 ha2
        linarith
      rw [le_div_iff₀ hpos] at this; linarith
  rcases eq_or_lt_of_le ht2 with h0 | hpos
  · obtain ⟨a2, ha2⟩ := feasible_nonempty P hP π y hy
    have := step1 a2 ha2
    rw [← h0] at this ⊢; simpa using this
  · have : T P π q y ≤ (T P π q (t1 * x + t2 * y) - t1 * T P π q x) / t2 := by
      apply T_le_of P π q y hy hP
      intro a2 ha2; rw [le_div_iff₀ hpos]
      have := step1 a2 ha2
      linarith
    rw [le_div_iff₀ hpos] at this; linarith

lemma T_mono_pi (P : Params) (hP : P.Standing) (π π' : ℝ) (hπ0 : 0 ≤ π) (hππ' : π < π')
    (hπ'1 : π' ≤ 1) (q : ℝ → ℝ) (hq : Bnd P q) (hc : ConcaveOn ℝ (Set.Ici 0) q)
    (v : ℝ) (hv : 0 ≤ v) : T P π q v ≤ T P π' q v := by
  have hπ'0 : 0 < π' := by linarith
  have hπ1 : π ≤ 1 := by linarith
  apply T_le_of P π q v hv hP
  intro a ha
  obtain ⟨α, hα⟩ : ∃ α, α = π / π' := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = (π' - π) / π' := ⟨_, rfl⟩
  have hα0 : 0 ≤ α := by rw [hα]; positivity
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact div_nonneg (by linarith) hπ'0.le
  have hαγ : α + γ = 1 := by rw [hα, hγ]; field_simp; ring
  have hπα : π' * α = π := by rw [hα]; field_simp
  have hπγ : π' * γ = π' - π := by rw [hγ]; field_simp
  clear hα hγ
  obtain ⟨b, hbdef⟩ : ∃ b : Policy, b = ⟨a.θ, α * a.udh + γ * a.unh, α * a.udl + γ * a.unl, a.unh, a.unl,
    α * a.wdh + γ * a.wnh, α * a.wdl + γ * a.wnl, a.wnh, a.wnl⟩ := ⟨_, rfl⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := ha
  have hb : Feasible P π' v b := by
    subst hbdef
    refine ⟨h1, h2, by positivity, by positivity, h5, h6,
      by positivity, by positivity, h9, h10, ?_, ?_, h13, ?_⟩
    · show α * a.udh + γ * a.unh + (α * a.wdh + γ * a.wnh) / (1 + P.r) ≥ a.unh + a.wnh / (1 + P.r)
      rw [V_mix]
      have := comb α γ _ _ _ _ hα0 hγ0 h11 (le_refl (a.unh + a.wnh / (1 + P.r)))
      have e : α * (a.unh + a.wnh / (1 + P.r)) + γ * (a.unh + a.wnh / (1 + P.r))
          = a.unh + a.wnh / (1 + P.r) := by linear_combination (a.unh + a.wnh / (1 + P.r)) * hαγ
      linarith
    · show α * a.udl + γ * a.unl + (α * a.wdl + γ * a.wnl) / (1 + P.r) ≥ a.unl + a.wnl / (1 + P.r)
      rw [V_mix]
      have := comb α γ _ _ _ _ hα0 hγ0 h12 (le_refl (a.unl + a.wnl / (1 + P.r)))
      have e : α * (a.unl + a.wnl / (1 + P.r)) + γ * (a.unl + a.wnl / (1 + P.r))
          = a.unl + a.wnl / (1 + P.r) := by linear_combination (a.unl + a.wnl / (1 + P.r)) * hαγ
      linarith
    · rw [h14]
      show (1 - a.θ) * _ = (1 - a.θ) * (π' * (P.p * (α * a.udh + γ * a.unh + (α * a.wdh + γ * a.wnh) / (1 + P.r))
        + (1 - P.p) * (α * a.udl + γ * a.unl + (α * a.wdl + γ * a.wnl) / (1 + P.r)))
        + (1 - π') * (P.p * (a.unh + a.wnh / (1 + P.r)) + (1 - P.p) * (a.unl + a.wnl / (1 + P.r))))
      rw [V_mix, V_mix]
      linear_combination (-(1 - a.θ)) * ((P.p * (a.udh + a.wdh / (1 + P.r)) + (1 - P.p) * (a.udl + a.wdl / (1 + P.r))) * hπα
        + (P.p * (a.unh + a.wnh / (1 + P.r)) + (1 - P.p) * (a.unl + a.wnl / (1 + P.r))) * hπγ)
  have hT := le_T P hP π' hπ'0.le hπ'1 q hq v b hb
  have cq : ∀ w1 w2 : ℝ, 0 ≤ w1 → 0 ≤ w2 → α * q w1 + γ * q w2 ≤ q (α * w1 + γ * w2) := by
    intro w1 w2 hw1 hw2
    have := hc.2 (Set.mem_Ici.2 hw1) (Set.mem_Ici.2 hw2) hα0 hγ0 hαγ
    simpa [smul_eq_mul] using this
  have d1 := cq _ _ h7 h9
  have d2 := cq _ _ h8 h10
  have hp0 := hP.2.2.1
  have hp1 : 0 ≤ 1 - P.p := by linarith [hP.2.2.2.1]
  have hE : E P π q a ≤ E P π' q b := by
    have e1 : E P π q a = π' * (P.p * (α * q a.wdh + γ * q a.wnh) + (1 - P.p) * (α * q a.wdl + γ * q a.wnl))
        + (1 - π') * (P.p * q a.wnh + (1 - P.p) * q a.wnl) := by
      simp only [E]
      linear_combination (-(P.p * q a.wdh + (1 - P.p) * q a.wdl)) * hπα
        - (P.p * q a.wnh + (1 - P.p) * q a.wnl) * hπγ
    have e2 : E P π' q b = π' * (P.p * q (α * a.wdh + γ * a.wnh) + (1 - P.p) * q (α * a.wdl + γ * a.wnl))
        + (1 - π') * (P.p * q a.wnh + (1 - P.p) * q a.wnl) := by subst hbdef; rfl
    rw [e1, e2]
    have := comb P.p (1 - P.p) _ _ _ _ hp0.le hp1 d1 d2
    linarith [mul_le_mul_of_nonneg_left this hπ'0.le]
  rw [objective_eq'] at hT ⊢
  have hθ : b.θ = a.θ := by subst hbdef; rfl
  rw [hθ] at hT
  have hk : 0 ≤ 1 - a.θ := by linarith
  have hr0 := hP.2.2.2.2.1
  have : E P π q a / (1 + P.r) ≤ E P π' q b / (1 + P.r) := div_le_div_of_nonneg_right hE (by linarith)
  linarith [mul_le_mul_of_nonneg_left this hk]

/-- value iteration -/
noncomputable def it (P : Params) (π : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => T P π (it P π n)

lemma it_props (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (n : ℕ) :
    Bnd P (it P π n) ∧ ConcaveOn ℝ (Set.Ici 0) (it P π n) ∧
      (∀ w, 0 ≤ w → it P π n w ≤ it P π (n + 1) w) ∧
      (∀ w, 0 ≤ w → it P π (n + 1) w ≤ it P π n w + P.sStar / (1 + P.r) ^ n) := by
  have hs := (basics P hP).2.2.1
  have hr0 := hP.2.2.2.2.1
  induction n with
  | zero =>
    have hb0 : Bnd P (it P π 0) := fun w _ => ⟨le_refl _, by simp [it]; linarith⟩
    refine ⟨hb0, concaveOn_const _ (convex_Ici 0), ?_, ?_⟩
    · intro w hw; simp only [it]; exact (T_bounds P hP π hπ0 hπ1 _ hb0 w hw).1
    · intro w hw; simp only [it, pow_zero, div_one, zero_add]
      exact (T_bounds P hP π hπ0 hπ1 _ hb0 w hw).2.1
  | succ n ih =>
    obtain ⟨hb, hc, hm, hst⟩ := ih
    have hb1 : Bnd P (it P π (n + 1)) := T_bnd P hP π hπ0 hπ1 _ hb
    refine ⟨hb1, T_concave P hP π hπ0 hπ1 _ hb hc, ?_, ?_⟩
    · intro w hw
      have := T_le_add P hP π hπ0 hπ1 _ _ hb hb1 0 (le_refl _) (by simpa using hm) w hw
      simpa [it] using this
    · intro w hw
      have := T_le_add P hP π hπ0 hπ1 _ _ hb1 hb (P.sStar / (1 + P.r) ^ n) (by positivity)
        (by simpa using hst) w hw
      have e : P.sStar / (1 + P.r) ^ n / (1 + P.r) = P.sStar / (1 + P.r) ^ (n + 1) := by
        rw [pow_succ, div_div]
      rw [e] at this
      simpa [it] using this

lemma small_le (C R d : ℝ) (hC : 0 < C) (hR : 1 < R) (h : ∀ n : ℕ, d ≤ C / R ^ n) : d ≤ 0 := by
  by_contra hd
  push Not at hd
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hd hC) (show 1 / R < 1 by rw [div_lt_one (by linarith)]; exact hR)
  have := h n
  have hRn : 0 < R ^ n := by positivity
  rw [div_pow, one_pow, div_lt_div_iff₀ hRn hC] at hn
  rw [le_div_iff₀ hRn] at this
  linarith


lemma it_mono_le (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (w : ℝ) (hw : 0 ≤ w) (m n : ℕ) (hmn : m ≤ n) : it P π m w ≤ it P π n w := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_refl _
  | succ n _ ih => exact le_trans ih ((it_props P hP π hπ0 hπ1 n).2.2.1 w hw)

lemma it_tail (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (w : ℝ) (hw : 0 ≤ w) (n k : ℕ) :
    it P π (n + k) w ≤ it P π n w + P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ n
      - P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ (n + k) := by
  have hr0 := hP.2.2.2.2.1
  induction k with
  | zero => simp
  | succ k ih =>
    have h := (it_props P hP π hπ0 hπ1 (n + k)).2.2.2 w hw
    have e : P.sStar / (1 + P.r) ^ (n + k) = P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ (n + k)
        - P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ (n + k + 1) := by
      rw [pow_succ]; field_simp; ring
    rw [← add_assoc]
    linarith

/-- the limit of value iteration -/
noncomputable def sv (P : Params) (π : ℝ) (w : ℝ) : ℝ := ⨆ n, it P π n w

lemma sv_props (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (w : ℝ) (hw : 0 ≤ w) (n : ℕ) :
    it P π n w ≤ sv P π w ∧ sv P π w ≤ it P π n w + P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ n
      ∧ sv P π w ≤ P.sStar := by
  have hr0 := hP.2.2.2.2.1
  have hs := (basics P hP).2.2.1
  have hbdd : BddAbove (Set.range fun m => it P π m w) :=
    ⟨P.sStar, by rintro _ ⟨m, rfl⟩; exact ((it_props P hP π hπ0 hπ1 m).1 w hw).2⟩
  refine ⟨le_ciSup hbdd n, ciSup_le fun m => ?_, ciSup_le fun m => ((it_props P hP π hπ0 hπ1 m).1 w hw).2⟩
  rcases le_total m n with h | h
  · have := it_mono_le P hP π hπ0 hπ1 w hw m n h
    have : 0 ≤ P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ n := by positivity
    linarith
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have := it_tail P hP π hπ0 hπ1 w hw n k
    have : 0 ≤ P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ (n + k) := by positivity
    linarith

lemma sv_bnd (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) :
    Bnd P (sv P π) := fun w hw =>
  ⟨le_trans (by simp [it]) (sv_props P hP π hπ0 hπ1 w hw 0).1, (sv_props P hP π hπ0 hπ1 w hw 0).2.2⟩

lemma sv_fixed (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (v : ℝ) (hv : 0 ≤ v) : sv P π v = T P π (sv P π) v := by
  have hr0 := hP.2.2.2.2.1
  have hs := (basics P hP).2.2.1
  have hb := sv_bnd P hP π hπ0 hπ1
  apply le_antisymm
  · apply ciSup_le
    intro n
    have h1 := (it_props P hP π hπ0 hπ1 n).2.2.1 v hv
    have h2 := T_le_add P hP π hπ0 hπ1 _ _ (it_props P hP π hπ0 hπ1 n).1 hb 0 (le_refl _)
      (fun w hw => by simpa using (sv_props P hP π hπ0 hπ1 w hw n).1) v hv
    simp only [zero_div, add_zero] at h2
    exact le_trans h1 h2
  · have : T P π (sv P π) v - sv P π v ≤ 0 := by
      apply small_le (P.sStar * (1 + P.r) / P.r) (1 + P.r) _ (by positivity) (by linarith)
      intro n
      have h2 := T_le_add P hP π hπ0 hπ1 _ _ hb (it_props P hP π hπ0 hπ1 n).1
        (P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ n) (by positivity)
        (fun w hw => (sv_props P hP π hπ0 hπ1 w hw n).2.1) v hv
      have h3 := (sv_props P hP π hπ0 hπ1 v hv (n + 1)).1
      have e : P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ n / (1 + P.r)
          ≤ P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ n := by
        apply div_le_self (by positivity) (by linarith)
      change T P π (sv P π) v ≤ it P π (n + 1) v + _ at h2
      linarith
    linarith

lemma sv_concave (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) :
    ConcaveOn ℝ (Set.Ici 0) (sv P π) := by
  have hr0 := hP.2.2.2.2.1
  have hs := (basics P hP).2.2.1
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy t1 t2 ht1 ht2 ht
  simp only [smul_eq_mul]
  rw [Set.mem_Ici] at hx hy
  have hz : 0 ≤ t1 * x + t2 * y := by positivity
  have : t1 * sv P π x + t2 * sv P π y - sv P π (t1 * x + t2 * y) ≤ 0 := by
    apply small_le (P.sStar * (1 + P.r) / P.r) (1 + P.r) _ (by positivity) (by linarith)
    intro n
    have h1 := (sv_props P hP π hπ0 hπ1 x hx n).2.1
    have h2 := (sv_props P hP π hπ0 hπ1 y hy n).2.1
    have h3 := (sv_props P hP π hπ0 hπ1 _ hz n).1
    have h4 := ((it_props P hP π hπ0 hπ1 n).2.1).2 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 hy) ht1 ht2 ht
    simp only [smul_eq_mul] at h4
    have := mul_le_mul_of_nonneg_left h1 ht1
    have := mul_le_mul_of_nonneg_left h2 ht2
    have e : t1 * (P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ n)
        + t2 * (P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ n) = P.sStar * (1 + P.r) / P.r / (1 + P.r) ^ n := by
      rw [← add_mul, ht, one_mul]
    nlinarith
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

lemma inF_of (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (s : ℝ → ℝ) (hb : Bnd P s) (hc : ConcaveOn ℝ (Set.Ici 0) s)
    (hfix : ∀ v, 0 ≤ v → s v = T P π s v) : InF P s := by
  obtain ⟨hδ, _, hss, _, _, _⟩ := basics P hP
  refine ⟨hc.continuousOn_Ici ?_, hb⟩
  apply cont_at_zero s (P.p * P.δ) P.sStar (mul_pos hP.2.2.1 hδ) hss
  intro v hv
  rw [hfix v hv]
  exact ⟨(T_bounds P hP π hπ0 hπ1 s hb v hv).1, (T_bounds P hP π hπ0 hπ1 s hb v hv).2.2⟩

lemma exists_value (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) :
    IsValue P π (sv P π) :=
  ⟨inF_of P hP π hπ0 hπ1 _ (sv_bnd P hP π hπ0 hπ1) (sv_concave P hP π hπ0 hπ1)
    (sv_fixed P hP π hπ0 hπ1), sv_fixed P hP π hπ0 hπ1⟩

/-- comparison principle -/
lemma compare (P : Params) (hP : P.Standing) (π1 π2 : ℝ) (h10 : 0 ≤ π1) (h11 : π1 ≤ 1)
    (h20 : 0 ≤ π2) (h21 : π2 ≤ 1) (s1 s2 : ℝ → ℝ) (hs1 : IsValue P π1 s1) (hs2 : IsValue P π2 s2)
    (hT : ∀ v, 0 ≤ v → T P π1 s1 v ≤ T P π2 s1 v) : ∀ v, 0 ≤ v → s1 v ≤ s2 v := by
  have hr0 := hP.2.2.2.2.1
  have hs := (basics P hP).2.2.1
  have hb1 : Bnd P s1 := hs1.1.2
  have hb2 : Bnd P s2 := hs2.1.2
  have key : ∀ n : ℕ, ∀ v, 0 ≤ v → s1 v ≤ s2 v + P.sStar / (1 + P.r) ^ n := by
    intro n
    induction n with
    | zero => intro v hv; simp; linarith [(hb1 v hv).2, (hb2 v hv).1]
    | succ n ih =>
      intro v hv
      have := T_le_add P hP π2 h20 h21 s1 s2 hb1 hb2 _ (by positivity) ih v hv
      rw [hs1.2 v hv, hs2.2 v hv]
      have e : P.sStar / (1 + P.r) ^ n / (1 + P.r) = P.sStar / (1 + P.r) ^ (n + 1) := by
        rw [pow_succ, div_div]
      linarith [hT v hv]
  intro v hv
  have := small_le P.sStar (1 + P.r) (s1 v - s2 v) hs (by linarith) (fun n => by linarith [key n v hv])
  linarith

lemma value_unique (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (s1 s2 : ℝ → ℝ) (hs1 : IsValue P π s1) (hs2 : IsValue P π s2) : ∀ v, 0 ≤ v → s1 v = s2 v :=
  fun v hv => le_antisymm
    (compare P hP π π hπ0 hπ1 hπ0 hπ1 s1 s2 hs1 hs2 (fun _ _ => le_refl _) v hv)
    (compare P hP π π hπ0 hπ1 hπ0 hπ1 s2 s1 hs2 hs1 (fun _ _ => le_refl _) v hv)

lemma value_concave (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (s : ℝ → ℝ) (hs : IsValue P π s) : ConcaveOn ℝ (Set.Ici 0) s :=
  (sv_concave P hP π hπ0 hπ1).congr (fun v hv =>
    value_unique P hP π hπ0 hπ1 _ _ (exists_value P hP π hπ0 hπ1) hs v hv)

lemma value_mono (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (s : ℝ → ℝ) (hs : IsValue P π s) : MonotoneOn s (Set.Ici 0) := by
  intro x hx y hy hxy
  rw [Set.mem_Ici] at hx hy
  rw [hs.2 x hx, hs.2 y hy]
  exact T_mono_v P hP π hπ0 hπ1 s hs.1.2 x y hx hxy

lemma value_top (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (s : ℝ → ℝ) (hs : IsValue P π s) : ∀ v, P.vBar ≤ v → s v = P.sStar := by
  obtain ⟨_, hμ, hss, hid, hvb, _⟩ := basics P hP
  have hr0 := hP.2.2.2.2.1
  have hR : (0:ℝ) < 1 + P.r := by linarith
  have hb := hs.1.2
  have h1 : s P.vBar = P.sStar := by
    have := T_ge_vbar P hP π hπ0 hπ1 s hb P.vBar (le_refl _)
    rw [← hs.2 _ hvb.le] at this
    have hle := (hb _ hvb.le).2
    apply le_antisymm hle
    -- s v̄ ≥ μ + s v̄ / R  ⇒  s v̄ ≥ s*
    have e : P.sStar - P.sStar / (1 + P.r) = P.μ := by linarith
    have : (P.sStar - s P.vBar) * (1 - 1 / (1 + P.r)) ≤ 0 := by
      have : (P.sStar - s P.vBar) * (1 - 1 / (1 + P.r)) = P.sStar - P.sStar / (1 + P.r)
          - (s P.vBar - s P.vBar / (1 + P.r)) := by ring
      linarith
    have hpos : 0 < 1 - 1 / (1 + P.r) := by
      rw [sub_pos, div_lt_one hR]; linarith
    nlinarith
  intro v hv
  have hv0 : 0 ≤ v := le_trans hvb.le hv
  apply le_antisymm (hb v hv0).2
  have := T_ge_vbar P hP π hπ0 hπ1 s hb v hv
  rw [← hs.2 v hv0, h1] at this
  linarith

/-- weak comparative statics in π -/
lemma value_mono_pi (P : Params) (hP : P.Standing) (π π' : ℝ) (hπ0 : 0 ≤ π) (hππ' : π < π')
    (hπ'1 : π' ≤ 1) (s s' : ℝ → ℝ) (hs : IsValue P π s) (hs' : IsValue P π' s') :
    ∀ v, 0 ≤ v → s v ≤ s' v := by
  have hπ1 : π ≤ 1 := by linarith
  have hc := value_concave P hP π hπ0 hπ1 s hs
  exact compare P hP π π' hπ0 hπ1 (by linarith) hπ'1 s s' hs hs'
    (fun v hv => T_mono_pi P hP π π' hπ0 hππ' hπ'1 s hs.1.2 hc v hv)


lemma bracket_lower (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (a : Policy) (v : ℝ) (ha : Feasible P π v a) :
    P.p * P.δ + (a.unl + a.wnl / (1 + P.r)) ≤ Bk P π a := by
  obtain ⟨hθ0, hθ1, hu1, hu2, hu3, hu4, hw1, hw2, hw3, hw4, hg, hb, hn, hpk⟩ := ha
  have hp0 := hP.2.2.1
  have hp1 := hP.2.2.2.1
  unfold Bk
  have hp1' : (0:ℝ) ≤ 1 - P.p := by linarith
  have hπ1' : (0:ℝ) ≤ 1 - π := by linarith
  set Vnl := a.unl + a.wnl / (1 + P.r)
  have e1 : P.p * P.δ + Vnl ≤ P.p * (a.udh + a.wdh / (1 + P.r)) + (1 - P.p) * (a.udl + a.wdl / (1 + P.r)) := by
    nlinarith [mul_le_mul_of_nonneg_left (show P.δ + Vnl ≤ a.udh + a.wdh / (1 + P.r) by linarith) hp0.le,
      mul_le_mul_of_nonneg_left (show Vnl ≤ a.udl + a.wdl / (1 + P.r) by linarith) hp1']
  have e2 : P.p * P.δ + Vnl ≤ P.p * (a.unh + a.wnh / (1 + P.r)) + (1 - P.p) * Vnl := by
    nlinarith [mul_le_mul_of_nonneg_left (show P.δ + Vnl ≤ a.unh + a.wnh / (1 + P.r) by linarith) hp0.le]
  nlinarith [mul_le_mul_of_nonneg_left e1 hπ0, mul_le_mul_of_nonneg_left e2 hπ1']

lemma E_le_gap (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (s : ℝ → ℝ) (hb : Bnd P s) (a : Policy) (v : ℝ) (ha : Feasible P π v a) (γ : ℝ)
    (hsw : s a.wnl ≤ P.sStar - γ) : E P π s a ≤ P.sStar - (1 - π) * (1 - P.p) * γ := by
  obtain ⟨_, _, _, _, _, _, hw1, hw2, hw3, hw4, _⟩ := ha
  have b1 := (hb _ hw1).2
  have b2 := (hb _ hw2).2
  have b3 := (hb _ hw3).2
  have hp0 := hP.2.2.1
  have hp1 := hP.2.2.2.1
  unfold E
  have hp1' : (0:ℝ) ≤ 1 - P.p := by linarith
  have hπ1' : (0:ℝ) ≤ 1 - π := by linarith
  have e1 : P.p * s a.wdh + (1 - P.p) * s a.wdl ≤ P.sStar := by
    nlinarith [mul_le_mul_of_nonneg_left b1 hp0.le, mul_le_mul_of_nonneg_left b2 hp1']
  have e2 : P.p * s a.wnh + (1 - P.p) * s a.wnl ≤ P.sStar - (1 - P.p) * γ := by
    nlinarith [mul_le_mul_of_nonneg_left b3 hp0.le, mul_le_mul_of_nonneg_left hsw hp1']
  nlinarith [mul_le_mul_of_nonneg_left e1 hπ0, mul_le_mul_of_nonneg_left e2 hπ1']

lemma obj_le_gap (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (s : ℝ → ℝ) (hb : Bnd P s) (a : Policy) (v : ℝ) (ha : Feasible P π v a) (γ : ℝ)
    (hsw : s a.wnl ≤ P.sStar - γ) :
    objective P π s a ≤ max (P.sStar - (1 - π) * (1 - P.p) * γ / (1 + P.r)) 0 := by
  have hE := E_le_gap P hP π hπ0 hπ1 s hb a v ha γ hsw
  obtain ⟨_, _, _, hid, _, _⟩ := basics P hP
  have hR : (0:ℝ) < 1 + P.r := by linarith [hP.2.2.2.2.1]
  have hk0 : 0 ≤ 1 - a.θ := by linarith [ha.2.1]
  have hk1 : 1 - a.θ ≤ 1 := by linarith [ha.1]
  rw [objective_eq']
  have h1 : P.μ + E P π s a / (1 + P.r) ≤ P.sStar - (1 - π) * (1 - P.p) * γ / (1 + P.r) := by
    have : E P π s a / (1 + P.r) ≤ (P.sStar - (1 - π) * (1 - P.p) * γ) / (1 + P.r) :=
      div_le_div_of_nonneg_right hE hR.le
    have e : (P.sStar - (1 - π) * (1 - P.p) * γ) / (1 + P.r)
        = P.sStar / (1 + P.r) - (1 - π) * (1 - P.p) * γ / (1 + P.r) := by ring
    linarith
  generalize P.sStar - (1 - π) * (1 - P.p) * γ / (1 + P.r) = X at h1 ⊢
  generalize P.μ + E P π s a / (1 + P.r) = Y at h1 ⊢
  generalize 1 - a.θ = k at hk0 hk1 ⊢
  rcases le_total X 0 with hX | hX
  · rw [max_eq_right hX]; nlinarith
  · rw [max_eq_left hX]; nlinarith

lemma obj_le_bracket (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (s : ℝ → ℝ) (hb : Bnd P s) (a : Policy) (m c : ℝ) (hm : 0 ≤ m) (hc : 0 < c)
    (ha : Feasible P π m a) (hB : m + c ≤ Bk P π a) :
    objective P π s a ≤ P.sStar * m / (m + c) := by
  have hob := (obj_bounds P hP π hπ0 hπ1 s hb a m ha).2
  have hpk := pk_eq P π m a ha
  have hk0 : 0 ≤ 1 - a.θ := by linarith [ha.2.1]
  have hss := (basics P hP).2.2.1
  have hk : (1 - a.θ) * (m + c) ≤ m := by
    have := mul_le_mul_of_nonneg_left hB hk0
    linarith
  rw [le_div_iff₀ (by linarith)]
  generalize objective P π s a = O at hob ⊢
  generalize 1 - a.θ = k at hk hk0 hob
  nlinarith [mul_le_mul_of_nonneg_left hk hss.le]

/-- below `v̄` the firm value is strictly below first best -/
lemma value_lt_top (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π < 1)
    (s : ℝ → ℝ) (hs : IsValue P π s) (m : ℝ) (hm0 : 0 ≤ m) (hmv : m < P.vBar)
    (hbelow : ∀ w, 0 ≤ w → w < m → s w < P.sStar) : s m < P.sStar := by
  obtain ⟨hδ, hμ, hss, hid, hvb, hvb2⟩ := basics P hP
  have hr0 := hP.2.2.2.2.1
  have hp1 := hP.2.2.2.1
  have hR : (0:ℝ) < 1 + P.r := by linarith
  have hb : Bnd P s := hs.1.2
  obtain ⟨η, hη⟩ : ∃ η, η = P.r * (P.vBar - m) / 2 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = P.r * (P.vBar - m) / (2 * (1 + P.r)) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; apply div_pos (mul_pos hr0 (by linarith)) (by linarith)
  have hη0 : 0 < η := by rw [hη]; exact div_pos (mul_pos hr0 (by linarith)) two_pos
  have hηc : P.p * P.δ + (m - η) / (1 + P.r) = m + c := by
    have : P.p * P.δ = P.vBar - P.vBar / (1 + P.r) := by linarith
    rw [this, hη, hc]; field_simp; ring
  obtain ⟨γ, hγ0, hγs⟩ : ∃ γ, 0 < γ ∧ ∀ w, 0 ≤ w → w ≤ m - η → s w ≤ P.sStar - γ := by
    by_cases hmη : 0 ≤ m - η
    · have hlt := hbelow (m - η) hmη (by linarith)
      refine ⟨P.sStar - s (m - η), by linarith, fun w hw hwle => ?_⟩
      have := value_mono P hP π hπ0 hπ1.le s hs (Set.mem_Ici.2 hw) (Set.mem_Ici.2 hmη) hwle
      linarith
    · exact ⟨1, one_pos, fun w hw hwle => absurd (le_trans hw hwle) hmη⟩
  have hκ0 : 0 < (1 - π) * (1 - P.p) * γ / (1 + P.r) :=
    div_pos (mul_pos (mul_pos (by linarith) (by linarith)) hγ0) hR
  have hT : T P π s m ≤ max (max (P.sStar - (1 - π) * (1 - P.p) * γ / (1 + P.r)) 0)
      (P.sStar * m / (m + c)) := by
    apply T_le_of P π s m hm0 hP
    intro a ha
    by_cases hw : a.wnl ≤ m - η
    · exact le_trans (obj_le_gap P hP π hπ0 hπ1.le s hb a m ha γ (hγs a.wnl ha.2.2.2.2.2.2.2.2.2.1 hw))
        (le_max_left _ _)
    · push Not at hw
      have hbl := bracket_lower P hP π hπ0 hπ1.le a m ha
      have hVnl : a.wnl / (1 + P.r) ≤ a.unl + a.wnl / (1 + P.r) := by linarith [ha.2.2.2.2.2.1]
      have hdiv : (m - η) / (1 + P.r) < a.wnl / (1 + P.r) := div_lt_div_of_pos_right hw hR
      exact le_trans (obj_le_bracket P hP π hπ0 hπ1.le s hb a m c hm0 hc0 ha (by linarith))
        (le_max_right _ _)
  have hMlt : max (max (P.sStar - (1 - π) * (1 - P.p) * γ / (1 + P.r)) 0) (P.sStar * m / (m + c))
      < P.sStar := by
    apply max_lt (max_lt (by linarith) hss)
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  rw [hs.2 m hm0]
  linarith

end VDAux

open VDAux in
theorem solution (P : Params) (hP : P.Standing) (π : ℝ) (hπ0 : 0 ≤ π) (hπ1 : π < 1)
    (s : ℝ → ℝ) (hs : IsValue P π s) :
    sInf {v : ℝ | 0 ≤ v ∧ s v = P.sStar} = P.vBar := by
  obtain ⟨_, _, _, _, hvb, _⟩ := basics P hP
  set A := {v : ℝ | 0 ≤ v ∧ s v = P.sStar} with hA
  have hvbA : P.vBar ∈ A := ⟨hvb.le, value_top P hP π hπ0 hπ1.le s hs _ (le_refl _)⟩
  have hbdd : BddBelow A := ⟨0, fun v hv => hv.1⟩
  have hne : A.Nonempty := ⟨_, hvbA⟩
  have hclosed : IsClosed A := by
    have : A = Set.Ici 0 ∩ s ⁻¹' {P.sStar} := by
      ext v; simp [hA, Set.mem_Ici]
    rw [this]
    exact hs.1.1.preimage_isClosed_of_isClosed isClosed_Ici isClosed_singleton
  have hmA : sInf A ∈ A := hclosed.csInf_mem hne hbdd
  apply le_antisymm (csInf_le hbdd hvbA)
  by_contra hlt
  push Not at hlt
  have := value_lt_top P hP π hπ0 hπ1 s hs (sInf A) hmA.1 hlt (fun w hw hwm => by
    by_contra hc
    push Not at hc
    have hwA : w ∈ A := ⟨hw, le_antisymm (hs.1.2 w hw).2 hc⟩
    exact absurd (csInf_le hbdd hwA) (not_le.2 hwm))
  rw [hmA.2] at this
  exact lt_irrefl _ this
