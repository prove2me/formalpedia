-- Prove2me | solution 1 for RenewForward.PriceImpact.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T12:19:34.422297+00:00
-- url     : https://prove2.me/submissions/582a6fff-a7fd-4350-b325-2d10f54d62f9

import Mathlib
import Definitions.Def_RenewForward_PriceImpact_Setting
import Definitions.Def_RenewForward_PriceImpact_ClosedForms
import Theorems.Thm_RenewForward_PriceImpact_theorem_1
import Theorems.Thm_RenewForward_PriceImpact_prop2_derivative
import Theorems.Thm_RenewForward_PriceImpact_prop2_sign
import Theorems.Thm_RenewForward_PriceImpact_prop2_forward

open RenewForward.PriceImpact MeasureTheory ProbabilityTheory

theorem solution (M : Params) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (θ ξ : Ω → ℝ) (hS : Standing M P θ ξ)
    (hmu : 0 < muXi P ξ)
    (hζ : 27 / (4 * (M.NR : ℝ)) ≤ cvXi P ξ * tauNXi P ξ) :
    (∀ kW : ℝ, 0 ≤ kW → ∃ f1 f2 pf : ℝ, IsFwdEq M P θ ξ kW f1 f2 pf) ∧
    ∃ ks kf : ℝ, 0 < ks ∧ 0 ≤ kf ∧
      ∀ e : ℝ → ℝ × ℝ × ℝ,
        (∀ kW : ℝ, 0 ≤ kW → IsFwdEq M P θ ξ kW (e kW).1 (e kW).2.1 (e kW).2.2) →
        StrictAntiOn (fun kW => ∫ w, spotP M θ ξ kW ((e kW).1 + (e kW).2.1) w ∂P) (Set.Icc 0 ks) ∧
        StrictMonoOn (fun kW => ∫ w, spotP M θ ξ kW ((e kW).1 + (e kW).2.1) w ∂P) (Set.Ici ks) ∧
        StrictMonoOn (fun kW => (e kW).2.2) (Set.Ici kf) := by
  obtain ⟨hθm, hξm, _hind, ⟨lo, hi, hθb⟩, hξb, hlam, hNR, hvT, hvX⟩ := hS
  set m := momentsOf P θ ξ with hm
  have hN : (1 : ℝ) ≤ M.NR := by exact_mod_cast hNR
  have hs2X : 0 < m.s2X := hvX
  have hs2T : 0 < m.s2T := hvT
  have hmuX : 0 < m.muX := hmu
  -- the skewness condition in polynomial form
  have hζ' : 27 * m.muX * m.s2X ≤ 4 * (M.NR : ℝ) * m.tauX := by
    have hsq : 0 < Real.sqrt m.s2X := Real.sqrt_pos.2 hs2X
    have hprod : cvXi P ξ * tauNXi P ξ = m.tauX / (m.muX * m.s2X) := by
      simp only [cvXi, tauNXi]
      change Real.sqrt m.s2X / m.muX * (m.tauX / Real.sqrt m.s2X ^ 3) = _
      have h3 : Real.sqrt m.s2X ^ 3 = m.s2X * Real.sqrt m.s2X := by
        rw [pow_succ, Real.sq_sqrt hs2X.le]
      rw [h3]; field_simp
    rw [hprod, div_le_div_iff₀ (by positivity) (by positivity)] at hζ
    linarith
  have hpos : 0 < 2 * m.muX * m.s2X + m.tauX := by
    have : 0 < 27 * m.muX * m.s2X := by positivity
    have : 0 < m.tauX := by nlinarith
    positivity
  -- integrability
  have hθi : Integrable θ P := by
    refine Integrable.of_bound hθm.aestronglyMeasurable (max |lo| |hi|) (Filter.Eventually.of_forall ?_)
    intro w
    have := hθb w
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h1 := neg_abs_le lo; have h2 := le_max_left |lo| |hi|; linarith [this.1]
    · have h1 := le_abs_self hi; have h2 := le_max_right |lo| |hi|; linarith [this.2]
  have hξi : Integrable ξ P := by
    refine Integrable.of_bound hξm.aestronglyMeasurable 1 (Filter.Eventually.of_forall ?_)
    intro w
    have := hξb w
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [this.1, this.2]
  have hT1 := fun kW (hkW : 0 ≤ kW) =>
    theorem_1 M P θ ξ ⟨hθm, hξm, _hind, ⟨lo, hi, hθb⟩, hξb, hlam, hNR, hvT, hvX⟩ kW hkW
  -- expected spot price at the closed form
  have hEs : ∀ kW, 0 ≤ kW →
      ∫ w, spotP M θ ξ kW (fStar M m kW + fStar M m kW) w ∂P = expSpotClosed M m kW := by
    intro kW hkW
    have h2 := (hT1 kW hkW).2
    rw [integral_congr_ae (Filter.Eventually.of_forall fun w => (h2 w).2)]
    simp only [p0, expSpotClosed, meanP0]
    have hc : Integrable (fun _ : Ω => M.a + 2 * M.c) P := integrable_const _
    have h2 : Integrable (fun w => M.a + 2 * M.c + θ w) P := hc.add hθi
    have h3 : Integrable (fun w => ξ w * kW) P := hξi.mul_const kW
    have h4 : Integrable (fun w => M.a + 2 * M.c + θ w - ξ w * kW) P := h2.sub h3
    have h5 : Integrable (fun w => (M.a + 2 * M.c + θ w - ξ w * kW) / 3) P := h4.div_const 3
    rw [integral_sub h5 (integrable_const _), integral_div, integral_const, integral_sub h2 h3,
      integral_add hc hθi, integral_const, integral_mul_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rfl
  have hEq : ∀ e : ℝ → ℝ × ℝ × ℝ,
      (∀ kW : ℝ, 0 ≤ kW → IsFwdEq M P θ ξ kW (e kW).1 (e kW).2.1 (e kW).2.2) →
      ∀ kW, 0 ≤ kW → (e kW).1 = fStar M m kW ∧ (e kW).2.1 = fStar M m kW ∧
        (e kW).2.2 = fwdPriceClosed M m kW := by
    intro e he kW hkW
    obtain ⟨h1, h2, h3⟩ := ((hT1 kW hkW).1 _ _ _).1 (he kW hkW)
    exact ⟨h1, h2, h3⟩
  obtain ⟨_, _, _, ks, hks0, _, hneg, hposs⟩ :=
    prop2_sign M m hlam hNR hmuX hs2X hs2T.le hζ'
  obtain ⟨kf', hkf'⟩ := prop2_forward M m hlam hNR hs2X hs2T.le hpos
  have hder := fun k => (prop2_derivative M m hlam hNR hs2T.le hs2X.le k)
  have hcontE : Continuous (expSpotClosed M m) :=
    continuous_iff_continuousAt.2 fun k => (hder k).2.continuousAt
  have hderivE : ∀ k, deriv (expSpotClosed M m) k
      = spsPoly M m k / (9 * (M.NR : ℝ) ^ 2 * nuFwd M m k ^ 2) := fun k => (hder k).2.deriv
  have hdenpos : ∀ k, 0 < 9 * (M.NR : ℝ) ^ 2 * nuFwd M m k ^ 2 := fun k => by
    have := (hder k).1; positivity
  have hanti : StrictAntiOn (expSpotClosed M m) (Set.Icc 0 ks) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 ks) hcontE.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [hderivE]
    exact div_neg_of_neg_of_pos (hneg x ⟨hx.1.le, hx.2⟩) (hdenpos x)
  have hmono : StrictMonoOn (expSpotClosed M m) (Set.Ici ks) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici ks) hcontE.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    rw [hderivE]
    exact div_pos (hposs x hx) (hdenpos x)
  set kf := max kf' 0
  have hfmono : StrictMonoOn (fwdPriceClosed M m) (Set.Ici kf) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici kf)
    · intro x hx
      have : kf' ≤ x := le_trans (le_max_left _ _) hx
      exact (differentiableAt_of_deriv_ne_zero (hkf' x this).ne').continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      exact hkf' x (le_trans (le_max_left _ _) (le_of_lt hx))
  refine ⟨fun kW hkW => ⟨_, _, _, ((hT1 kW hkW).1 _ _ _).2 ⟨rfl, rfl, rfl⟩⟩,
    ks, kf, hks0, le_max_right _ _, fun e he => ⟨?_, ?_, ?_⟩⟩
  · intro a ha b hb hab
    have ea := hEq e he a ha.1
    have eb := hEq e he b hb.1
    simp only
    rw [ea.1, ea.2.1, eb.1, eb.2.1, hEs a ha.1, hEs b hb.1]
    exact hanti ha hb hab
  · intro a ha b hb hab
    have ha0 : 0 ≤ a := le_trans hks0.le ha
    have hb0 : 0 ≤ b := le_trans hks0.le hb
    have ea := hEq e he a ha0
    have eb := hEq e he b hb0
    simp only
    rw [ea.1, ea.2.1, eb.1, eb.2.1, hEs a ha0, hEs b hb0]
    exact hmono ha hb hab
  · intro a ha b hb hab
    have ha0 : 0 ≤ a := le_trans (le_max_right _ _) ha
    have hb0 : 0 ≤ b := le_trans (le_max_right _ _) hb
    simp only
    rw [(hEq e he a ha0).2.2, (hEq e he b hb0).2.2]
    exact hfmono ha hb hab
