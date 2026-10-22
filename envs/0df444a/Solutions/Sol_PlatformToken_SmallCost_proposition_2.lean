-- Prove2me | solution 1 for PlatformToken.SmallCost.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T05:49:19.619745+00:00
-- url     : https://prove2.me/submissions/3c9fadc3-33de-4209-960e-3628a6c4f03d

import Mathlib
import Definitions.Def_PlatformToken_SmallCost_Setting
import Definitions.Def_PlatformToken_SmallCost_Programs

set_option autoImplicit false

open PlatformToken.SmallCost

namespace PT2

/-- Young's inequality in the form used. -/
lemma young (a μ A e : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hμ : 0 < μ) (hA : 0 ≤ A) (he : 0 ≤ e) :
    A * e ^ a ≤ μ * e + (1 - a) * (A * (a / μ) ^ a) ^ (1 / (1 - a)) := by
  set W := (A * (a / μ) ^ a) ^ (1 / (1 - a)) with hW
  have hX : 0 ≤ A * (a / μ) ^ a := mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
  have hW0 : 0 ≤ W := Real.rpow_nonneg hX _
  have h1a : (1 - a) ≠ 0 := by linarith
  have hWp : W ^ (1 - a) = A * (a / μ) ^ a := by
    rw [hW, ← Real.rpow_mul hX, one_div, inv_mul_cancel₀ h1a, Real.rpow_one]
  have key := Real.geom_mean_le_arith_mean2_weighted (w₁ := a) (w₂ := 1 - a)
    (p₁ := μ * e / a) (p₂ := W) ha0.le (by linarith) (by positivity) hW0 (by ring)
  rw [hWp] at key
  have h2 : (μ * e / a) ^ a = (μ / a) ^ a * e ^ a := by
    rw [show μ * e / a = (μ / a) * e by ring, Real.mul_rpow (by positivity) he]
  have h3 : (μ / a) ^ a * (a / μ) ^ a = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    rw [show μ / a * (a / μ) = 1 by field_simp]
    simp
  have h4 : (μ * e / a) ^ a * (A * (a / μ) ^ a) = A * e ^ a := by
    rw [h2]; linear_combination (A * e ^ a) * h3
  have h5 : a * (μ * e / a) = μ * e := by field_simp
  linarith

section
variable (p : Params)

lemma d_mul_Q (e Q : ℝ) (hQ : 0 < Q) : d p e Q * Q = e ^ p.a * Q ^ (1 - p.b) := by
  unfold d
  rw [show (1 - p.b) = -p.b + 1 by ring, Real.rpow_add_one hQ.ne']
  ring

lemma F_eq (e Q : ℝ) (hQ : 0 < Q) :
    F p e Q = e ^ p.a * Q ^ (1 - p.b) - p.m * Q ^ (p.n + 1) := by
  unfold F s
  rw [Real.rpow_add_one hQ.ne', ← d_mul_Q p e Q hQ]
  ring

lemma Fe_mul_e (e Q : ℝ) (he : 0 < e) : Fe p e Q * e = p.a * (e ^ p.a * Q ^ (1 - p.b)) := by
  unfold Fe
  rw [Real.rpow_sub_one he.ne']
  field_simp

lemma de_mul_Q (e Q : ℝ) (hQ : 0 < Q) : de p e Q * Q = Fe p e Q := by
  unfold de Fe
  rw [show (1 - p.b) = -p.b + 1 by ring, Real.rpow_add_one hQ.ne']
  ring

lemma obj_eq (e Q : ℝ) (hQ : 0 < Q) :
    obj p e Q = (e ^ p.a * Q ^ (1 - p.b) - p.m * Q ^ (p.n + 1)) / (1 - p.δ) - p.c * Q
      - p.K * Q ^ p.k - p.γ * e := by
  unfold obj Ccap
  rw [F_eq p e Q hQ]

end


noncomputable def Bnd (p : Params) (μ Q : ℝ) : ℝ :=
  (1 - p.a) * (Q ^ (1 - p.b) / (1 - p.δ) * (p.a / μ) ^ p.a) ^ (1 / (1 - p.a))

section
variable (p : Params) (hp : p.Standing)
include hp

lemma obj_le (μ e Q : ℝ) (hμ : 0 < μ) (he : 0 ≤ e) (hQ : 0 < Q) :
    obj p e Q ≤ μ * e + Bnd p μ Q - p.γ * e - p.m * Q ^ (p.n + 1) / (1 - p.δ) - p.c * Q
      - p.K * Q ^ p.k := by
  rw [obj_eq p e Q hQ]
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  have hy := young p.a μ (Q ^ (1 - p.b) / (1 - p.δ)) e hp.a_pos (by linarith [hp.a_lt_b, hp.b_lt_one])
    hμ (by positivity) he
  have : (e ^ p.a * Q ^ (1 - p.b) - p.m * Q ^ (p.n + 1)) / (1 - p.δ)
      = Q ^ (1 - p.b) / (1 - p.δ) * e ^ p.a - p.m * Q ^ (p.n + 1) / (1 - p.δ) := by ring
  rw [this]; unfold Bnd; linarith

lemma Bnd_eq (μ Q : ℝ) (hμ : 0 < μ) (hQ : 0 ≤ Q) :
    Bnd p μ Q = (1 - p.a) * ((p.a / μ) ^ p.a / (1 - p.δ)) ^ (1 / (1 - p.a)) *
      Q ^ ((1 - p.b) / (1 - p.a)) := by
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  have ha := hp.a_pos
  unfold Bnd
  rw [show Q ^ (1 - p.b) / (1 - p.δ) * (p.a / μ) ^ p.a
      = Q ^ (1 - p.b) * ((p.a / μ) ^ p.a / (1 - p.δ)) by ring,
    Real.mul_rpow (Real.rpow_nonneg hQ _) (by positivity), ← Real.rpow_mul hQ]
  rw [show (1 - p.b) * (1 / (1 - p.a)) = (1 - p.b) / (1 - p.a) by ring]
  ring

lemma r_pos : 0 < (1 - p.b) / (1 - p.a) :=
  div_pos (by linarith [hp.b_lt_one]) (by linarith [hp.a_lt_b, hp.b_lt_one])

lemma r_lt_one : (1 - p.b) / (1 - p.a) < 1 := by
  rw [div_lt_one (by linarith [hp.a_lt_b, hp.b_lt_one])]; linarith [hp.a_lt_b]

lemma Bnd_mono (μ Q Q' : ℝ) (hμ : 0 < μ) (hQ : 0 ≤ Q) (hQQ : Q ≤ Q') :
    Bnd p μ Q ≤ Bnd p μ Q' := by
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  have ha := hp.a_pos
  rw [Bnd_eq p hp μ Q hμ hQ, Bnd_eq p hp μ Q' hμ (hQ.trans hQQ)]
  apply mul_le_mul_of_nonneg_left
  · exact Real.rpow_le_rpow hQ hQQ (r_pos p hp).le
  · apply mul_nonneg (by linarith [hp.a_lt_b, hp.b_lt_one]); positivity

lemma Bnd_nonneg (μ Q : ℝ) (hμ : 0 < μ) (hQ : 0 ≤ Q) : 0 ≤ Bnd p μ Q := by
  have := Bnd_mono p hp μ 0 Q hμ le_rfl hQ
  have h0 : Bnd p μ 0 = 0 := by
    rw [Bnd_eq p hp μ 0 hμ le_rfl, Real.zero_rpow (r_pos p hp).ne']; ring
  linarith

lemma Qstar (hcm : 0 < p.c ∨ 0 < p.m) :
    ∃ Qs, 1 ≤ Qs ∧ ∀ Q, Qs ≤ Q → Bnd p p.γ Q ≤ p.c * Q + p.m * Q ^ (p.n + 1) / (1 - p.δ) := by
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  have ha := hp.a_pos
  have hγ := hp.γ_pos
  set r := (1 - p.b) / (1 - p.a) with hr
  set G := (1 - p.a) * ((p.a / p.γ) ^ p.a / (1 - p.δ)) ^ (1 / (1 - p.a)) with hG
  have hG0 : 0 ≤ G := by
    apply mul_nonneg (by linarith [hp.a_lt_b, hp.b_lt_one]); positivity
  set L := p.c + p.m / (1 - p.δ) with hL
  have hL0 : 0 < L := by
    rcases hcm with h | h
    · have : 0 ≤ p.m / (1 - p.δ) := div_nonneg hp.m_nonneg hD.le
      linarith
    · have : 0 < p.m / (1 - p.δ) := div_pos h hD
      linarith [hp.c_nonneg]
  have ht := tendsto_rpow_neg_atTop (y := 1 - r) (by linarith [r_lt_one p hp])
  have hev := (ht.eventually (gt_mem_nhds (show (0:ℝ) < L / (G + 1) by positivity)))
  rcases Filter.eventually_atTop.mp hev with ⟨N, hN⟩
  refine ⟨max N 1, le_max_right _ _, fun Q hQ => ?_⟩
  have hQ1 : 1 ≤ Q := le_trans (le_max_right _ _) hQ
  have hQ0 : 0 < Q := by linarith
  have hQN : N ≤ Q := le_trans (le_max_left _ _) hQ
  have h1 := hN Q hQN
  rw [Bnd_eq p hp _ Q hγ hQ0.le]
  have hsplit : Q ^ r = Q ^ (-(1 - r)) * Q := by
    rw [show r = -(1 - r) + 1 by ring, Real.rpow_add_one hQ0.ne']; ring_nf
  have hpow : Q ≤ Q ^ (p.n + 1) := by
    rw [Real.rpow_add_one hQ0.ne']
    have : 1 ≤ Q ^ p.n := Real.one_le_rpow hQ1 hp.n_nonneg
    nlinarith
  have hGQ : G * Q ^ r ≤ L * Q := by
    rw [hsplit]
    have h2 : G * Q ^ (-(1 - r)) ≤ L := by
      calc G * Q ^ (-(1 - r)) ≤ G * (L / (G + 1)) := by
            apply mul_le_mul_of_nonneg_left h1.le hG0
        _ ≤ L := by
            rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  have hm : p.m * Q / (1 - p.δ) ≤ p.m * Q ^ (p.n + 1) / (1 - p.δ) := by
    apply div_le_div_of_nonneg_right _ hD.le
    exact mul_le_mul_of_nonneg_left hpow hp.m_nonneg
  have : L * Q = p.c * Q + p.m * Q / (1 - p.δ) := by rw [hL]; ring
  linarith

lemma Bnd_small (η : ℝ) (hη : 0 < η) :
    ∃ ql, 0 < ql ∧ ∀ Q, 0 ≤ Q → Q < ql → Bnd p p.γ Q < η := by
  have hγ := hp.γ_pos
  have hc : ContinuousAt (fun Q : ℝ => Q ^ ((1 - p.b) / (1 - p.a))) 0 :=
    Real.continuousAt_rpow_const 0 _ (Or.inr (r_pos p hp).le)
  set G := (1 - p.a) * ((p.a / p.γ) ^ p.a / (1 - p.δ)) ^ (1 / (1 - p.a)) with hG
  have hc2 : ContinuousAt (fun Q : ℝ => G * Q ^ ((1 - p.b) / (1 - p.a))) 0 := hc.const_mul G
  have h0 : G * (0:ℝ) ^ ((1 - p.b) / (1 - p.a)) = 0 := by
    rw [Real.zero_rpow (r_pos p hp).ne']; ring
  have hev := hc2.eventually (gt_mem_nhds (show G * (0:ℝ) ^ ((1 - p.b) / (1 - p.a)) < η by
    rw [h0]; exact hη))
  rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδ, hball⟩
  refine ⟨δ, hδ, fun Q hQ0 hQ => ?_⟩
  rw [Bnd_eq p hp _ Q hγ hQ0]
  apply hball
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hQ0]; exact hQ

end


/-- The block-chain first-order condition times `e`: `h(e,Q)·e` up to the factor. -/
noncomputable def Hf (p : Params) (e Q : ℝ) : ℝ :=
  p.a * (e ^ p.a * Q ^ (1 - p.b)) / (1 - p.δ) - p.a * Ccap p Q - p.γ * e

section
variable (p : Params) (hp : p.Standing)
include hp

lemma ivt (Q e1 : ℝ) (hQ : 0 < Q) (he1 : 0 < e1) (hH : 0 < Hf p e1 Q) (hC : 0 ≤ Ccap p Q) :
    ∃ eB, e1 < eB ∧ Hf p eB Q = 0 := by
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  have ha := hp.a_pos
  have hγ := hp.γ_pos
  set A := p.a * Q ^ (1 - p.b) / (1 - p.δ) with hA
  have hA0 : 0 ≤ A := by positivity
  set W0 := (1 - p.a) * (A * (p.a / (p.γ / 2)) ^ p.a) ^ (1 / (1 - p.a)) with hW0
  have hW00 : 0 ≤ W0 := by
    apply mul_nonneg (by linarith [hp.a_lt_b, hp.b_lt_one])
    apply Real.rpow_nonneg; exact mul_nonneg hA0 (Real.rpow_nonneg (by positivity) _)
  have hHe : ∀ e, Hf p e Q = A * e ^ p.a - p.a * Ccap p Q - p.γ * e := by
    intro e; unfold Hf; rw [hA]; ring
  set M := e1 + 2 * W0 / p.γ + 1 with hM
  have hM0 : 0 ≤ M := by positivity
  have hyM := young p.a (p.γ / 2) A M ha (by linarith [hp.a_lt_b, hp.b_lt_one]) (by positivity) hA0 hM0
  have hHM : Hf p M Q < 0 := by
    rw [hHe]
    have : p.γ * M = p.γ * e1 + 2 * W0 + p.γ := by rw [hM]; field_simp
    have : 0 ≤ p.a * Ccap p Q := mul_nonneg ha.le hC
    nlinarith
  have hle : e1 ≤ M := by
    have : 0 ≤ 2 * W0 / p.γ := by positivity
    rw [hM]; linarith
  have hcont : ContinuousOn (fun e => Hf p e Q) (Set.Icc e1 M) := by
    have : Continuous fun e : ℝ => Hf p e Q := by
      simp only [hHe]
      have := Real.continuous_rpow_const (q := p.a) ha.le
      fun_prop
    exact this.continuousOn
  have h0 : (0:ℝ) ∈ Set.Icc (Hf p M Q) (Hf p e1 Q) := ⟨hHM.le, hH.le⟩
  obtain ⟨eB, ⟨heB1, heB2⟩, heB⟩ := intermediate_value_Icc' hle hcont h0
  refine ⟨eB, lt_of_le_of_ne heB1 ?_, heB⟩
  intro h
  rw [← h] at heB
  simp only at heB
  linarith

lemma blockPt (Q eB : ℝ) (hQ : 0 < Q) (heB : 0 < eB) (hH : Hf p eB Q = 0)
    (hv : p.v * Ccap p Q ≤ eB ^ p.a * Q ^ (1 - p.b)) (hC : 0 ≤ Ccap p Q) :
    (Q, p.v * Ccap p Q / (eB ^ p.a * Q ^ (1 - p.b)), eB) ∈ BlockFeasible p ∧
    obj p eB Q = ((1 - p.a) * (eB ^ p.a * Q ^ (1 - p.b)) - p.m * Q ^ (p.n + 1)) / (1 - p.δ)
      - p.c * Q - (1 - p.a) * Ccap p Q := by
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  have ha := hp.a_pos
  have hγ := hp.γ_pos
  have hv1 : 0 < p.v := by linarith [hp.one_le_v]
  set u := eB ^ p.a * Q ^ (1 - p.b) with hu
  have hu0 : 0 < u := by positivity
  have hFe := Fe_mul_e p eB Q heB
  have hde := de_mul_Q p eB Q hQ
  have hdQ := d_mul_Q p eB Q hQ
  rw [← hu] at hFe hdQ
  unfold Hf at hH; rw [← hu] at hH
  refine ⟨⟨?_, ?_, hQ.le, heB.le, by positivity, ?_⟩, ?_⟩
  · simp only
    have e1 : p.v * Ccap p Q / u * (1 / p.v) * de p eB Q * Q = Ccap p Q * Fe p eB Q / u := by
      rw [mul_assoc _ (de p eB Q) Q, hde]; field_simp
    rw [e1]
    have hFe' : Fe p eB Q = p.a * u / eB := by rw [← hFe]; field_simp
    rw [hFe']
    have hH' := hH
    field_simp at hH'
    field_simp
    linear_combination hH'
  · simp only
    rw [mul_assoc, hdQ]; field_simp
  · simp only; rw [div_le_one hu0]; exact hv
  · rw [obj_eq p eB Q hQ, ← hu]
    unfold Ccap at hH ⊢
    have hγe : p.γ * eB = p.a * u / (1 - p.δ) - p.a * (p.K * Q ^ p.k) := by linarith
    rw [hγe]
    ring

lemma compare (Q eT eB : ℝ) (hQ : 0 < Q) (heT : 0 < eT) (hlt : eT < eB) (hH : Hf p eB Q = 0)
    (hC : 0 < Ccap p Q) : obj p eT Q < obj p eB Q := by
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  have ha := hp.a_pos
  have heB : 0 < eB := by linarith
  -- tangent line inequality for `x ↦ x^a`
  have htan : eT ^ p.a * eB ≤ eB ^ p.a * eB + p.a * eB ^ p.a * (eT - eB) := by
    have h := rpow_one_add_le_one_add_mul_self (s := eT / eB - 1) (by
      have : 0 ≤ eT / eB := by positivity
      linarith) (p := p.a) ha.le (by linarith [hp.a_lt_b, hp.b_lt_one])
    rw [show 1 + (eT / eB - 1) = eT / eB by ring, Real.div_rpow heT.le heB.le] at h
    have hpos : 0 < eB ^ p.a := by positivity
    rw [div_le_iff₀ hpos] at h
    have : (1 + p.a * (eT / eB - 1)) * eB ^ p.a * eB = eB ^ p.a * eB + p.a * eB ^ p.a * (eT - eB) := by
      field_simp
    nlinarith
  rw [obj_eq p eT Q hQ, obj_eq p eB Q hQ]
  unfold Hf at hH
  unfold Ccap at hC hH
  set X := Q ^ (1 - p.b) with hX
  have hX0 : 0 < X := by positivity
  set tB := eB ^ p.a
  set tT := eT ^ p.a
  -- goal: (tT X - M)/D - γ eT < (tB X - M)/D - γ eB
  have key : p.γ * (eB - eT) * eB < X * (tB - tT) * eB / (1 - p.δ) := by
    have h1 : p.γ * eB = p.a * (tB * X) / (1 - p.δ) - p.a * (p.K * Q ^ p.k) := by linarith
    have h2 : X * (tB - tT) * eB ≥ X * (p.a * tB * (eB - eT)) := by
      have := mul_le_mul_of_nonneg_left htan hX0.le
      nlinarith
    have h3 : p.γ * (eB - eT) * eB = (p.a * (tB * X) / (1 - p.δ) - p.a * (p.K * Q ^ p.k)) * (eB - eT) := by
      rw [← h1]; ring
    rw [h3]
    have h4 : X * (p.a * tB * (eB - eT)) / (1 - p.δ) ≤ X * (tB - tT) * eB / (1 - p.δ) :=
      div_le_div_of_nonneg_right h2 hD.le
    have h5 : (p.a * (tB * X) / (1 - p.δ) - p.a * (p.K * Q ^ p.k)) * (eB - eT)
        < X * (p.a * tB * (eB - eT)) / (1 - p.δ) := by
      have : 0 < p.a * (p.K * Q ^ p.k) * (eB - eT) := by
        have : 0 < eB - eT := by linarith
        positivity
      have e : X * (p.a * tB * (eB - eT)) / (1 - p.δ)
          = p.a * (tB * X) / (1 - p.δ) * (eB - eT) := by ring
      rw [e]; nlinarith
    linarith
  have key2 : p.γ * (eB - eT) < X * (tB - tT) / (1 - p.δ) := by
    have : X * (tB - tT) * eB / (1 - p.δ) = X * (tB - tT) / (1 - p.δ) * eB := by ring
    rw [this] at key
    exact lt_of_mul_lt_mul_right key heB.le
  have : (tT * X - p.m * Q ^ (p.n + 1)) / (1 - p.δ) = X * tT / (1 - p.δ) - p.m * Q ^ (p.n + 1) / (1 - p.δ) := by ring
  have : (tB * X - p.m * Q ^ (p.n + 1)) / (1 - p.δ) = X * tB / (1 - p.δ) - p.m * Q ^ (p.n + 1) / (1 - p.δ) := by ring
  have : X * (tB - tT) / (1 - p.δ) = X * tB / (1 - p.δ) - X * tT / (1 - p.δ) := by ring
  linarith

end


section
variable (p : Params) (hp : p.Standing)
include hp

lemma sQ (Q : ℝ) (hQ : 0 < Q) : s p Q * Q = p.m * Q ^ (p.n + 1) := by
  unfold s; rw [Real.rpow_add_one hQ.ne']; ring

/-- Key comparison from the paper (Claim (i)): at a traditional-feasible point, `h(e,Q) > 0`. -/
lemma trad_key (hcm : 0 < p.c ∨ 0 < p.m) (hK : 0 < p.K) (x : ℝ × ℝ × ℝ)
    (hx : x ∈ TradFeasible p) : 0 < Hf p x.2.2 x.1 := by
  obtain ⟨hcon, hα, hQ, he, hα0, hα1⟩ := hx
  set Q := x.1
  set α := x.2.1
  set e := x.2.2
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  have hδ := hp.δ_pos
  have ha := hp.a_pos
  set u := e ^ p.a * Q ^ (1 - p.b) with hu
  have hu0 : 0 < u := by positivity
  set C := Ccap p Q with hC
  have hC0 : 0 < C := by rw [hC]; unfold Ccap; positivity
  set M := p.m * Q ^ (p.n + 1) with hM
  have hM0 : 0 ≤ M := mul_nonneg hp.m_nonneg (by positivity)
  have hpos : 0 < M + (1 - p.δ) * p.c * Q := by
    rcases hcm with h | h
    · have : 0 < (1 - p.δ) * p.c * Q := by positivity
      linarith
    · have : 0 < M := by rw [hM]; positivity
      have : 0 ≤ (1 - p.δ) * p.c * Q := mul_nonneg (mul_nonneg hD.le hp.c_nonneg) hQ.le
      linarith
  have hpi1 : pi1 p e Q = u - M - p.c * Q := by
    unfold pi1; rw [sub_mul, sub_mul, d_mul_Q p e Q hQ, sQ p hp Q hQ]
  have hpi2 : pi2 p e Q = u - M := by
    unfold pi2; rw [sub_mul, d_mul_Q p e Q hQ, sQ p hp Q hQ]
  -- γ e = (1-α) a u / D
  have hFe := Fe_mul_e p e Q he
  rw [← hu] at hFe
  have hγe : p.γ * e = (1 - α) * (p.a * u) / (1 - p.δ) := by
    rw [← hcon, ← hFe]; ring
  have hHf : Hf p e Q = p.a * (α * u - (1 - p.δ) * C) / (1 - p.δ) := by
    unfold Hf; rw [← hu, ← hC, hγe]; field_simp; ring
  rw [hHf]
  apply div_pos _ hD
  apply mul_pos ha
  -- now α u > D C
  unfold alpha19 at hα
  rw [hpi1, hpi2, ← hC] at hα
  set num := C - min (u - M - p.c * Q) 0
  set den := u - M - p.c * Q + p.δ / (1 - p.δ) * (u - M) - min (u - M - p.c * Q) 0
  have hnum : C ≤ num := by have := min_le_right (u - M - p.c * Q) 0; linarith
  have hden : 0 < den := by
    by_contra hcon'
    push_neg at hcon'
    have : num / den ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by linarith) hcon'
    linarith
  have hαden : α * den = num := by rw [hα]; field_simp
  by_cases hcase : 0 ≤ u - M - p.c * Q
  · have hmin : min (u - M - p.c * Q) 0 = 0 := min_eq_right hcase
    have hnum' : num = C := by simp only [num, hmin]; ring
    have hden' : den * (1 - p.δ) = u - M - (1 - p.δ) * p.c * Q := by
      simp only [den, hmin]; field_simp; ring
    have : α * (u - M - (1 - p.δ) * p.c * Q) = (1 - p.δ) * C := by
      rw [← hden', ← mul_assoc, hαden, hnum']; ring
    nlinarith
  · push_neg at hcase
    have hmin : min (u - M - p.c * Q) 0 = u - M - p.c * Q := min_eq_left hcase.le
    have hnum' : num = C - (u - M - p.c * Q) := by simp only [num, hmin]
    have hden' : den * (1 - p.δ) = p.δ * (u - M) := by
      simp only [den, hmin]; field_simp; ring
    have h1 : α * (p.δ * (u - M)) = (1 - p.δ) * (C - (u - M - p.c * Q)) := by
      rw [← hden', ← mul_assoc, hαden, hnum']; ring
    have h2 : 0 < u - M := by
      have : 0 < (1 - p.δ) * (C - (u - M - p.c * Q)) := by
        apply mul_pos hD; linarith
      rw [← h1] at this
      by_contra h3; push_neg at h3
      have : α * (p.δ * (u - M)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hα0.le (mul_nonpos_of_nonneg_of_nonpos hδ.le h3)
      linarith
    have h3 : α * (p.δ * (u - M)) < α * (u - M) := by
      apply mul_lt_mul_of_pos_left _ hα0
      nlinarith [hp.δ_lt_one]
    have h4 : α * (u - M) ≤ α * u := by nlinarith
    have h5 : (1 - p.δ) * C < (1 - p.δ) * (C - (u - M - p.c * Q)) := by
      apply mul_lt_mul_of_pos_left _ hD; linarith
    linarith

lemma obj_le_u (x : ℝ × ℝ × ℝ) (hQ : 0 < x.1) (he : 0 < x.2.2) (hK : 0 ≤ p.K) :
    (1 - p.δ) * obj p x.2.2 x.1 ≤ x.2.2 ^ p.a * x.1 ^ (1 - p.b) := by
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  rw [obj_eq p _ _ hQ]
  have h1 : 0 ≤ p.m * x.1 ^ (p.n + 1) := mul_nonneg hp.m_nonneg (by positivity)
  have h2 : 0 ≤ p.c * x.1 := mul_nonneg hp.c_nonneg hQ.le
  have h3 : 0 ≤ p.K * x.1 ^ p.k := mul_nonneg hK (by positivity)
  have h4 : 0 ≤ p.γ * x.2.2 := mul_nonneg hp.γ_pos.le he.le
  have : (1 - p.δ) * ((x.2.2 ^ p.a * x.1 ^ (1 - p.b) - p.m * x.1 ^ (p.n + 1)) / (1 - p.δ)
      - p.c * x.1 - p.K * x.1 ^ p.k - p.γ * x.2.2) = x.2.2 ^ p.a * x.1 ^ (1 - p.b)
      - p.m * x.1 ^ (p.n + 1) - (1 - p.δ) * (p.c * x.1 + p.K * x.1 ^ p.k + p.γ * x.2.2) := by
    field_simp; ring
  rw [this]
  nlinarith

end


lemma standing_withK (p : Params) (hp : p.Standing) (K : ℝ) (hK : 0 ≤ K) : (withK p K).Standing :=
  { a_pos := hp.a_pos, a_lt_b := hp.a_lt_b, b_lt_one := hp.b_lt_one, m_nonneg := hp.m_nonneg,
    n_nonneg := hp.n_nonneg, K_nonneg := hK, k_gt := hp.k_gt, one_le_v := hp.one_le_v,
    δ_pos := hp.δ_pos, δ_lt_one := hp.δ_lt_one, c_nonneg := hp.c_nonneg, γ_pos := hp.γ_pos }

lemma k_pos (p : Params) (hp : p.Standing) : 0 < p.k :=
  lt_of_le_of_lt (div_nonneg (by linarith [hp.b_lt_one]) (by linarith [hp.a_lt_b, hp.b_lt_one]))
    hp.k_gt

section
variable (p : Params) (hp : p.Standing)
include hp

lemma trad_to_block (hcm : 0 < p.c ∨ 0 < p.m) (hK : 0 < p.K) (x : ℝ × ℝ × ℝ)
    (hx : x ∈ TradFeasible p) (hv : p.v * Ccap p x.1 ≤ (1 - p.δ) * obj p x.2.2 x.1) :
    ∃ y ∈ BlockFeasible p, obj p x.2.2 x.1 < obj p y.2.2 y.1 := by
  have hH := trad_key p hp hcm hK x hx
  obtain ⟨_, _, hQ, he, _, _⟩ := hx
  have hC : 0 < Ccap p x.1 := by unfold Ccap; positivity
  obtain ⟨eB, hlt, hB⟩ := ivt p hp x.1 x.2.2 hQ he hH hC.le
  have heB : 0 < eB := by linarith
  have hu : x.2.2 ^ p.a * x.1 ^ (1 - p.b) ≤ eB ^ p.a * x.1 ^ (1 - p.b) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Real.rpow_le_rpow he.le hlt.le hp.a_pos.le
  have hou := obj_le_u p hp x hQ he hK.le
  obtain ⟨hy, _⟩ := blockPt p hp x.1 eB hQ heB hB (by linarith) hC.le
  exact ⟨_, hy, compare p hp x.1 x.2.2 eB hQ he hlt hB hC⟩

end

lemma block_lower (p : Params) (hp : p.Standing) :
    ∃ η1 > 0, ∃ ε1 > 0, ∀ K, 0 < K → K ≤ ε1 →
      ∃ y ∈ BlockFeasible (withK p K), η1 ≤ obj (withK p K) y.2.2 y.1 := by
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  have ha := hp.a_pos
  have ha1 : p.a < 1 := by linarith [hp.a_lt_b, hp.b_lt_one]
  have hγ := hp.γ_pos
  have hv1 : 0 < p.v := by linarith [hp.one_le_v]
  set M0 := max (p.γ * (1 - p.δ) / p.a) ((p.m + (1 - p.δ) * p.c) / (1 - p.a)) with hM0
  have hM0a : p.γ * (1 - p.δ) / p.a ≤ M0 := le_max_left _ _
  have hM0b : (p.m + (1 - p.δ) * p.c) / (1 - p.a) ≤ M0 := le_max_right _ _
  have hM00 : 0 < M0 := lt_of_lt_of_le (by positivity) hM0a
  set Q1 := (M0 + 1) ^ (1 / (p.a - p.b)) with hQ1
  have hab : p.a - p.b ≠ 0 := by linarith [hp.a_lt_b]
  have hQ10 : 0 < Q1 := by positivity
  have hQ11 : Q1 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith)
    (div_neg_of_pos_of_neg one_pos (by linarith [hp.a_lt_b]))
  have hQpow : Q1 ^ (p.a - p.b) = M0 + 1 := by
    rw [hQ1, ← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hab, Real.rpow_one]
  set u1 := Q1 ^ p.a * Q1 ^ (1 - p.b) with hu1
  have hu1' : u1 = (M0 + 1) * Q1 := by
    rw [hu1, ← Real.rpow_add hQ10, show p.a + (1 - p.b) = (p.a - p.b) + 1 by ring,
      Real.rpow_add_one hQ10.ne', hQpow]
  have hu10 : 0 < u1 := by rw [hu1']; positivity
  set H0 := p.a * u1 / (1 - p.δ) - p.γ * Q1 with hH0
  have hH00 : 0 < H0 := by
    rw [hH0, hu1']
    have h1 : p.γ * (1 - p.δ) < p.a * (M0 + 1) := by
      rw [div_le_iff₀ ha] at hM0a; nlinarith
    have : p.γ * Q1 < p.a * ((M0 + 1) * Q1) / (1 - p.δ) := by
      rw [lt_div_iff₀ hD]; nlinarith
    linarith
  have hQn : Q1 ^ (p.n + 1) ≤ Q1 := by
    rw [Real.rpow_add_one hQ10.ne']
    have : Q1 ^ p.n ≤ 1 := Real.rpow_le_one hQ10.le hQ11.le hp.n_nonneg
    nlinarith
  set P0 := ((1 - p.a) * u1 - p.m * Q1 ^ (p.n + 1)) / (1 - p.δ) - p.c * Q1 with hP0
  have hP00 : 0 < P0 := by
    rw [hP0, hu1']
    have h1 : p.m + (1 - p.δ) * p.c < (1 - p.a) * (M0 + 1) := by
      rw [div_le_iff₀ (by linarith)] at hM0b; nlinarith
    have h2 : p.m * Q1 ^ (p.n + 1) ≤ p.m * Q1 := mul_le_mul_of_nonneg_left hQn hp.m_nonneg
    have : p.c * Q1 < ((1 - p.a) * ((M0 + 1) * Q1) - p.m * Q1) / (1 - p.δ) := by
      rw [lt_div_iff₀ hD]; nlinarith
    have : ((1 - p.a) * ((M0 + 1) * Q1) - p.m * Q1) / (1 - p.δ)
        ≤ ((1 - p.a) * ((M0 + 1) * Q1) - p.m * Q1 ^ (p.n + 1)) / (1 - p.δ) :=
      div_le_div_of_nonneg_right (by linarith) hD.le
    linarith
  refine ⟨P0 / 2, by positivity, min (P0 / 2) (min (H0 / 2) (u1 / p.v)),
    by positivity, fun K hK hKε => ?_⟩
  have hKP : K ≤ P0 / 2 := le_trans hKε (min_le_left _ _)
  have hKH : K ≤ H0 / 2 := le_trans hKε (le_trans (min_le_right _ _) (min_le_left _ _))
  have hKu : K ≤ u1 / p.v := le_trans hKε (le_trans (min_le_right _ _) (min_le_right _ _))
  set q := withK p K with hq
  have hqs : q.Standing := standing_withK p hp K hK.le
  have hQk : Q1 ^ p.k ≤ 1 := Real.rpow_le_one hQ10.le hQ11.le (k_pos p hp).le
  have hCq : Ccap q Q1 = K * Q1 ^ p.k := rfl
  have hC0 : 0 ≤ Ccap q Q1 := by rw [hCq]; positivity
  have hCK : Ccap q Q1 ≤ K := by rw [hCq]; nlinarith [Real.rpow_nonneg hQ10.le p.k]
  have hHq : Hf q Q1 Q1 = H0 - p.a * Ccap q Q1 := by
    show p.a * (Q1 ^ p.a * Q1 ^ (1 - p.b)) / (1 - p.δ) - p.a * Ccap q Q1 - p.γ * Q1 = _
    rw [hH0, hu1]; ring
  have hHpos : 0 < Hf q Q1 Q1 := by
    rw [hHq]; nlinarith
  obtain ⟨eB, hlt, hB⟩ := ivt q hqs Q1 Q1 hQ10 hQ10 hHpos hC0
  have heB : 0 < eB := by linarith
  have huB : u1 ≤ eB ^ p.a * Q1 ^ (1 - p.b) := by
    rw [hu1]; apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Real.rpow_le_rpow hQ10.le hlt.le ha.le
  have hvC : q.v * Ccap q Q1 ≤ eB ^ q.a * Q1 ^ (1 - q.b) := by
    show p.v * Ccap q Q1 ≤ eB ^ p.a * Q1 ^ (1 - p.b)
    rw [le_div_iff₀ hv1] at hKu
    nlinarith
  obtain ⟨hy, hobj⟩ := blockPt q hqs Q1 eB hQ10 heB hB hvC hC0
  refine ⟨_, hy, ?_⟩
  simp only
  rw [hobj]
  show P0 / 2 ≤ ((1 - p.a) * (eB ^ p.a * Q1 ^ (1 - p.b)) - p.m * Q1 ^ (p.n + 1)) / (1 - p.δ)
      - p.c * Q1 - (1 - p.a) * Ccap q Q1
  have : ((1 - p.a) * u1 - p.m * Q1 ^ (p.n + 1)) / (1 - p.δ)
      ≤ ((1 - p.a) * (eB ^ p.a * Q1 ^ (1 - p.b)) - p.m * Q1 ^ (p.n + 1)) / (1 - p.δ) := by
    apply div_le_div_of_nonneg_right _ hD.le
    have := mul_le_mul_of_nonneg_left huB (show (0:ℝ) ≤ 1 - p.a by linarith)
    linarith
  have h1a : (1 - p.a) * Ccap q Q1 ≤ Ccap q Q1 := by
    have := mul_le_mul_of_nonneg_right (show 1 - p.a ≤ 1 by linarith) hC0
    linarith
  linarith


section
variable (p : Params) (hp : p.Standing)
include hp

lemma obj_le' (μ e Q : ℝ) (hμ : 0 < μ) (he : 0 ≤ e) (hQ : 0 < Q) :
    obj p e Q ≤ μ * e + Bnd p μ Q - p.γ * e := by
  have h := obj_le p hp μ e Q hμ he hQ
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  have h1 : 0 ≤ p.m * Q ^ (p.n + 1) / (1 - p.δ) := div_nonneg (mul_nonneg hp.m_nonneg (by positivity)) hD.le
  have h2 : 0 ≤ p.c * Q := mul_nonneg hp.c_nonneg hQ.le
  have h3 : 0 ≤ p.K * Q ^ p.k := mul_nonneg hp.K_nonneg (by positivity)
  linarith

lemma obj_lt_Qs (Qs : ℝ)
    (hQs : ∀ Q, Qs ≤ Q → Bnd p p.γ Q ≤ p.c * Q + p.m * Q ^ (p.n + 1) / (1 - p.δ))
    (e Q : ℝ) (he : 0 ≤ e) (hQ : 0 < Q) (hpos : 0 < obj p e Q) : Q < Qs := by
  by_contra h; push_neg at h
  have h1 := obj_le p hp p.γ e Q hp.γ_pos he hQ
  have h2 := hQs Q h
  have h3 : 0 ≤ p.K * Q ^ p.k := mul_nonneg hp.K_nonneg (by positivity)
  linarith

lemma obj_le_Bmax (Qs : ℝ) (hQs1 : 0 ≤ Qs)
    (hQs : ∀ Q, Qs ≤ Q → Bnd p p.γ Q ≤ p.c * Q + p.m * Q ^ (p.n + 1) / (1 - p.δ))
    (e Q : ℝ) (he : 0 ≤ e) (hQ : 0 < Q) : obj p e Q ≤ Bnd p p.γ Qs := by
  have hB0 := Bnd_nonneg p hp p.γ Qs hp.γ_pos hQs1
  by_cases hpos : 0 < obj p e Q
  · have hlt := obj_lt_Qs p hp Qs hQs e Q he hQ hpos
    have := obj_le' p hp p.γ e Q hp.γ_pos he hQ
    have := Bnd_mono p hp p.γ Q Qs hp.γ_pos hQ.le hlt.le
    linarith
  · linarith

lemma block_pos (x : ℝ × ℝ × ℝ) (hx : x ∈ BlockFeasible p) : 0 < x.1 ∧ 0 < x.2.2 := by
  obtain ⟨h1, _, hQ, he, _, _⟩ := hx
  have hγ := hp.γ_pos
  have hb : 1 - p.b ≠ 0 := by linarith [hp.b_lt_one]
  have ha : p.a - 1 ≠ 0 := by linarith [hp.a_lt_b, hp.b_lt_one]
  constructor
  · rcases hQ.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at h1
      unfold Fe at h1
      rw [Real.zero_rpow hb] at h1
      simp at h1; linarith
  · rcases he.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at h1
      unfold Fe de at h1
      rw [Real.zero_rpow ha] at h1
      simp at h1; linarith

lemma trad_max (hcm : 0 < p.c ∨ 0 < p.m) (hK : 0 < p.K) (η : ℝ) (hη : 0 < η) (Qs : ℝ)
    (hQs1 : 1 ≤ Qs)
    (hQs : ∀ Q, Qs ≤ Q → Bnd p p.γ Q ≤ p.c * Q + p.m * Q ^ (p.n + 1) / (1 - p.δ))
    (hex : ∃ x ∈ TradFeasible p, η < obj p x.2.2 x.1) :
    ∃ x0 ∈ TradFeasible p, η ≤ obj p x0.2.2 x0.1 ∧ x0.1 ≤ Qs ∧
      ∀ x ∈ TradFeasible p, obj p x.2.2 x.1 ≤ obj p x0.2.2 x0.1 := by
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  have ha := hp.a_pos
  have hγ := hp.γ_pos
  obtain ⟨ql, hql, hqlB⟩ := Bnd_small p hp η hη
  set Eh := 2 * Bnd p (p.γ / 2) Qs / p.γ with hEh
  set box : Set (ℝ × ℝ × ℝ) := Set.Icc ql Qs ×ˢ (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) Eh) with hbox
  set f : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun x => (
      (1 - x.2.1) * (p.a * (x.2.2 ^ p.a * x.1 ^ (1 - p.b))) - p.γ * (1 - p.δ) * x.2.2,
      x.2.1 * (pi1 p x.2.2 x.1 + p.δ / (1 - p.δ) * pi2 p x.2.2 x.1 - min (pi1 p x.2.2 x.1) 0)
        - (Ccap p x.1 - min (pi1 p x.2.2 x.1) 0),
      obj p x.2.2 x.1) with hf
  set t : Set (ℝ × ℝ × ℝ) := {(0:ℝ)} ×ˢ ({(0:ℝ)} ×ˢ Set.Ici η) with ht
  set S := box ∩ f ⁻¹' t with hS
  have hQc : ∀ r : ℝ, ContinuousOn (fun x : ℝ × ℝ × ℝ => x.1 ^ r) box := by
    intro r
    apply ContinuousOn.rpow_const (by fun_prop)
    intro x hx; exact Or.inl (ne_of_gt (lt_of_lt_of_le hql hx.1.1))
  have hec : ContinuousOn (fun x : ℝ × ℝ × ℝ => x.2.2 ^ p.a) box :=
    ((Real.continuous_rpow_const ha.le).comp (by fun_prop)).continuousOn
  have hfc : ContinuousOn f box := by
    have h1 := hQc (1 - p.b)
    have h2 := hQc (-p.b)
    have h3 := hQc p.n
    have h4 := hQc p.k
    rw [hf]
    unfold pi1 pi2 obj F Ccap d s
    fun_prop
  have hboxc : IsCompact box := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have htc : IsClosed t := isClosed_singleton.prod (isClosed_singleton.prod isClosed_Ici)
  have hSc : IsClosed S := hfc.preimage_isClosed_of_isClosed hboxc.isClosed htc
  have hScpt : IsCompact S := hboxc.of_isClosed_subset hSc Set.inter_subset_left
  -- trad points with large objective lie in S
  have hin : ∀ x ∈ TradFeasible p, η ≤ obj p x.2.2 x.1 → x ∈ S := by
    intro x hx hobj
    obtain ⟨hcon, hα, hQ, he, hα0, hα1⟩ := hx
    have hpos : 0 < obj p x.2.2 x.1 := by linarith
    have hQs' := obj_lt_Qs p hp Qs hQs _ _ he.le hQ hpos
    have hQl : ql ≤ x.1 := by
      by_contra h; push_neg at h
      have := hqlB x.1 hQ.le h
      have := obj_le' p hp p.γ _ _ hγ he.le hQ
      linarith
    have hEe : x.2.2 ≤ Eh := by
      have h1 := obj_le' p hp (p.γ / 2) _ _ (by positivity) he.le hQ
      have h2 := Bnd_mono p hp (p.γ / 2) x.1 Qs (by positivity) hQ.le hQs'.le
      rw [hEh, le_div_iff₀ hγ]
      linarith
    refine ⟨⟨⟨hQl, hQs'.le⟩, ⟨hα0.le, hα1.le⟩, ⟨he.le, hEe⟩⟩, ?_⟩
    simp only [hf, ht, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Ici]
    refine ⟨?_, ?_, hobj⟩
    · have := Fe_mul_e p x.2.2 x.1 he
      rw [← this]
      have : (1 - x.2.1) * Fe p x.2.2 x.1 = p.γ * (1 - p.δ) := by
        rw [← hcon]; field_simp
      linear_combination x.2.2 * this
    · unfold alpha19 at hα
      set den := pi1 p x.2.2 x.1 + p.δ / (1 - p.δ) * pi2 p x.2.2 x.1 - min (pi1 p x.2.2 x.1) 0
      have hden : den ≠ 0 := by
        intro h0; rw [h0, div_zero] at hα; linarith
      rw [hα]; field_simp; ring
  obtain ⟨x1, hx1, hx1η⟩ := hex
  have hne : S.Nonempty := ⟨x1, hin x1 hx1 hx1η.le⟩
  have hobjc : ContinuousOn (fun x : ℝ × ℝ × ℝ => obj p x.2.2 x.1) S := by
    have := (continuous_snd.comp (continuous_snd)).continuousOn.mono (Set.subset_univ S)
    exact ((hfc.mono Set.inter_subset_left).snd).snd
  obtain ⟨x0, hx0S, hmax⟩ := hScpt.exists_isMaxOn hne hobjc
  obtain ⟨⟨⟨hQl0, hQs0⟩, ⟨hα00, hα01⟩, ⟨he00, _⟩⟩, hft⟩ := hx0S
  simp only [hf, ht, Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, Set.mem_Ici] at hft
  obtain ⟨heq1, heq2, hobj0⟩ := hft
  have hQ0 : 0 < x0.1 := lt_of_lt_of_le hql hQl0
  have he0 : 0 < x0.2.2 := by
    rcases he00.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [obj_eq p _ _ hQ0, ← h, Real.zero_rpow ha.ne'] at hobj0
      have h1 : 0 ≤ p.m * x0.1 ^ (p.n + 1) := mul_nonneg hp.m_nonneg (by positivity)
      have h2 : 0 ≤ p.c * x0.1 := mul_nonneg hp.c_nonneg hQ0.le
      have h3 : 0 ≤ p.K * x0.1 ^ p.k := mul_nonneg hp.K_nonneg (by positivity)
      have : (0 * x0.1 ^ (1 - p.b) - p.m * x0.1 ^ (p.n + 1)) / (1 - p.δ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le
      linarith
  have hnum : 0 < Ccap p x0.1 - min (pi1 p x0.2.2 x0.1) 0 := by
    have : 0 < Ccap p x0.1 := by unfold Ccap; positivity
    have := min_le_right (pi1 p x0.2.2 x0.1) 0
    linarith
  set den := pi1 p x0.2.2 x0.1 + p.δ / (1 - p.δ) * pi2 p x0.2.2 x0.1 - min (pi1 p x0.2.2 x0.1) 0
  have hden : den ≠ 0 := by
    intro h0; rw [h0] at heq2; linarith
  have hαne0 : x0.2.1 ≠ 0 := by
    intro h0; rw [h0] at heq2; linarith
  have hαne1 : x0.2.1 ≠ 1 := by
    intro h0; rw [h0] at heq1
    have : 0 < p.γ * (1 - p.δ) * x0.2.2 := by positivity
    linarith
  have hx0T : x0 ∈ TradFeasible p := by
    refine ⟨?_, ?_, hQ0, he0, lt_of_le_of_ne hα00 (Ne.symm hαne0), lt_of_le_of_ne hα01 hαne1⟩
    · have hFe := Fe_mul_e p x0.2.2 x0.1 he0
      have : (1 - x0.2.1) * Fe p x0.2.2 x0.1 * x0.2.2 = p.γ * (1 - p.δ) * x0.2.2 := by
        rw [mul_assoc, hFe]; linarith
      have h2 : (1 - x0.2.1) * Fe p x0.2.2 x0.1 = p.γ * (1 - p.δ) :=
        mul_right_cancel₀ he0.ne' this
      rw [h2]; field_simp
    · show x0.2.1 = (Ccap p x0.1 - min (pi1 p x0.2.2 x0.1) 0) / den
      rw [eq_div_iff hden]; linarith
  refine ⟨x0, hx0T, hobj0, hQs0, fun x hx => ?_⟩
  by_cases hxη : η ≤ obj p x.2.2 x.1
  · exact hmax (hin x hx hxη)
  · push_neg at hxη; linarith

end

end PT2

open PT2 in
theorem solution (p : Params) (hp : p.Standing) (hcm : 0 < p.c ∨ 0 < p.m) :
    ∃ ε > 0, ∀ K ∈ Set.Ioc 0 ε,
      BddAbove ((fun x : ℝ × ℝ × ℝ => obj (withK p K) x.2.2 x.1) '' TradFeasible (withK p K)) ∧
      BddAbove ((fun x : ℝ × ℝ × ℝ => obj (withK p K) x.2.2 x.1) '' BlockFeasible (withK p K)) ∧
      (PiTrad (withK p K) < PiBlock (withK p K) ∨
        (PiBlock (withK p K) = 0 ∧ PiTrad (withK p K) = 0)) := by
  have hD : 0 < 1 - p.δ := by linarith [hp.δ_lt_one]
  have hv1 : 0 < p.v := by linarith [hp.one_le_v]
  obtain ⟨η1, hη1, ε1, hε1, hblk⟩ := block_lower p hp
  obtain ⟨Qs, hQs1, hQs⟩ := Qstar p hp hcm
  have hQs0 : 0 < Qs := by linarith
  set η := η1 / 2 with hη
  have hη0 : 0 < η := by positivity
  set ε2 := (1 - p.δ) * η / (p.v * Qs ^ p.k) with hε2
  have hε20 : 0 < ε2 := by positivity
  refine ⟨min ε1 ε2, lt_min hε1 hε20, fun K hK => ?_⟩
  obtain ⟨hK0, hKε⟩ := hK
  have hK1 : K ≤ ε1 := le_trans hKε (min_le_left _ _)
  have hK2 : K ≤ ε2 := le_trans hKε (min_le_right _ _)
  set q := withK p K with hq
  have hqs : q.Standing := standing_withK p hp K hK0.le
  have hqK : 0 < q.K := hK0
  have hQsq : ∀ Q, Qs ≤ Q → Bnd q q.γ Q ≤ q.c * Q + q.m * Q ^ (q.n + 1) / (1 - q.δ) := hQs
  have hcmq : 0 < q.c ∨ 0 < q.m := hcm
  have hbT : BddAbove ((fun x : ℝ × ℝ × ℝ => obj q x.2.2 x.1) '' TradFeasible q) := by
    refine ⟨Bnd q q.γ Qs, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact obj_le_Bmax q hqs Qs hQs0.le hQsq _ _ hx.2.2.2.1.le hx.2.2.1
  have hbB : BddAbove ((fun x : ℝ × ℝ × ℝ => obj q x.2.2 x.1) '' BlockFeasible q) := by
    refine ⟨Bnd q q.γ Qs, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hQ, he⟩ := block_pos q hqs x hx
    exact obj_le_Bmax q hqs Qs hQs0.le hQsq _ _ he.le hQ
  refine ⟨hbT, hbB, Or.inl ?_⟩
  obtain ⟨y, hy, hyη⟩ := hblk K hK0 hK1
  have hsB : η1 ≤ sSup ((fun x : ℝ × ℝ × ℝ => obj q x.2.2 x.1) '' BlockFeasible q) :=
    le_trans hyη (le_csSup hbB ⟨y, hy, rfl⟩)
  have hPB : sSup ((fun x : ℝ × ℝ × ℝ => obj q x.2.2 x.1) '' BlockFeasible q) ≤ PiBlock q :=
    le_max_right _ _
  by_cases hex : ∃ x ∈ TradFeasible q, η < obj q x.2.2 x.1
  · obtain ⟨x0, hx0, hx0η, hx0Q, hmax⟩ := trad_max q hqs hcmq hqK η hη0 Qs hQs1 hQsq hex
    have hv : q.v * Ccap q x0.1 ≤ (1 - q.δ) * obj q x0.2.2 x0.1 := by
      show p.v * (K * x0.1 ^ p.k) ≤ (1 - p.δ) * obj q x0.2.2 x0.1
      have hQk : x0.1 ^ p.k ≤ Qs ^ p.k :=
        Real.rpow_le_rpow hx0.2.2.1.le hx0Q (k_pos p hp).le
      have hQk0 : 0 ≤ x0.1 ^ p.k := Real.rpow_nonneg hx0.2.2.1.le _
      have h1 : K * x0.1 ^ p.k ≤ ε2 * Qs ^ p.k :=
        mul_le_mul hK2 hQk hQk0 hε20.le
      have h2 : p.v * (ε2 * Qs ^ p.k) = (1 - p.δ) * η := by
        rw [hε2]; field_simp
      have h3 : (1 - p.δ) * η ≤ (1 - p.δ) * obj q x0.2.2 x0.1 :=
        mul_le_mul_of_nonneg_left hx0η hD.le
      have h4 := mul_le_mul_of_nonneg_left h1 hv1.le
      linarith
    obtain ⟨z, hz, hlt⟩ := trad_to_block q hqs hcmq hqK x0 hx0 hv
    have hsT : sSup ((fun x : ℝ × ℝ × ℝ => obj q x.2.2 x.1) '' TradFeasible q)
        ≤ obj q x0.2.2 x0.1 := by
      apply Real.sSup_le
      · rintro _ ⟨x, hx, rfl⟩; exact hmax x hx
      · linarith
    have hzB := le_csSup hbB ⟨z, hz, rfl⟩
    unfold PiTrad
    rw [max_lt_iff]
    constructor
    · linarith
    · linarith
  · push_neg at hex
    have hsT : sSup ((fun x : ℝ × ℝ × ℝ => obj q x.2.2 x.1) '' TradFeasible q) ≤ η := by
      apply Real.sSup_le
      · rintro _ ⟨x, hx, rfl⟩; exact hex x hx
      · linarith
    unfold PiTrad
    rw [max_lt_iff]
    constructor
    · linarith
    · linarith
