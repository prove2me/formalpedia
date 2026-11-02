-- Prove2me | solution 1 for ValueTrial.Asymptotic.equation_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:25:39.538518+00:00
-- url     : https://prove2.me/submissions/9c945bd3-3d32-4811-b677-a5c4c89bea2b

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter

namespace VBCT8

lemma integrable_pos (x : ℝ) :
    Integrable (fun v : ℝ => max (v - x) 0) (gaussianReal 0 1) := by
  have h1 : Integrable (fun v : ℝ => v) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
  exact (h1.sub (integrable_const x)).pos_part

lemma nl_eq (x : ℝ) :
    InventoryControl.normalLoss x = ∫ v, max (v - x) 0 ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, InventoryControl.normalLoss]
  have h1 : ∫ v in Set.Ioi x, (v - x) * gaussianPDFReal 0 1 v
      = ∫ v in Set.Ioi x, gaussianPDFReal 0 1 v • max (v - x) 0 := by
    refine setIntegral_congr_fun (measurableSet_Ioi (a := x)) ?_
    intro v hv
    simp only [Set.mem_Ioi] at hv
    simp only [smul_eq_mul]
    rw [max_eq_left (by linarith)]; ring
  rw [h1]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero ?_
  intro v hv
  simp only [Set.mem_Ioi, not_lt] at hv
  rw [max_eq_right (by linarith : v - x ≤ 0)]; simp

lemma gauss_eq (μ s : ℝ) (hs : s ≠ 0) :
    gaussianReal μ (s ^ 2).toNNReal = (gaussianReal 0 1).map (fun v => μ + s * v) := by
  have : (fun v : ℝ => μ + s * v) = (fun v => μ + v) ∘ (fun v => s * v) := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  congr 1
  · ring
  · ext; simp [sq_nonneg]

lemma int_shift (μ s k : ℝ) (hs : s ≠ 0) (a : ℝ) (ha : 0 < a) (x : ℝ)
    (hfx : ∀ v, max (μ + s * v - k) 0 = a * max (v - x) 0) :
    ∫ z, max (z - k) 0 ∂(gaussianReal μ (s ^ 2).toNNReal) = a * InventoryControl.normalLoss x := by
  rw [gauss_eq μ s hs, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [hfx]
  rw [integral_const_mul, nl_eq]

/-- `E (Z - k)^+ = s Ψ((k - μ)/s)` for `Z ~ N(μ, s²)`, `s > 0`. -/
lemma pos_part_gauss (μ s k : ℝ) (hs : 0 < s) :
    ∫ z, max (z - k) 0 ∂(gaussianReal μ (s ^ 2).toNNReal)
      = s * InventoryControl.normalLoss ((k - μ) / s) := by
  refine int_shift μ s k hs.ne' s hs _ (fun v => ?_)
  rw [mul_max_of_nonneg _ _ hs.le, mul_zero]
  congr 1; field_simp; ring

/-- `E (-Z - k)^+ = s Ψ((k + μ)/s)` for `Z ~ N(μ, s²)`, `s > 0`. -/
lemma neg_part_gauss (μ s k : ℝ) (hs : 0 < s) :
    ∫ z, max (-z - k) 0 ∂(gaussianReal μ (s ^ 2).toNNReal)
      = s * InventoryControl.normalLoss ((k + μ) / s) := by
  have hm : (gaussianReal μ (s ^ 2).toNNReal).map (fun z => -z)
      = gaussianReal (-μ) (s ^ 2).toNNReal := gaussianReal_map_neg
  have h := pos_part_gauss (-μ) s k hs
  rw [← hm, integral_map (by fun_prop) (by fun_prop)] at h
  rw [h]; congr 2; ring

lemma integrable_affine_pos (μ : ℝ) (v : NNReal) (a b : ℝ) :
    Integrable (fun z : ℝ => max (a * z - b) 0) (gaussianReal μ v) := by
  have h1 : Integrable (fun z : ℝ => z) (gaussianReal μ v) :=
    (memLp_id_gaussianReal (μ := μ) (v := v) 1).integrable le_rfl
  exact ((h1.const_mul a).sub (integrable_const b)).pos_part

end VBCT8

open ValueTrial.Asymptotic

theorem solution (θ : Params) (hS : θ.Standing) (ccap Ppop : ℝ → ℝ) (T r : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hP : 0 ≤ Ppop T) :
    let Pr := Prho θ (Ppop T)
    let sZ := sigZ θ (T * r / 2)
    let aN := θ.IN / ((1 - θ.pN) * Pr)
    let aS := θ.IS / (θ.pN * Pr)
    V θ ccap Ppop (T, r) =
      -(ccap r + θ.c * Ttil θ T * r) + θ.don * (Ttil θ T * r / 2) * (1 - 2 * θ.pN) * θ.mu0
        + Real.exp (-θ.rho * (T + θ.Del)) * Pr * sZ *
          ((1 - θ.pN) * InventoryControl.normalLoss ((aN - θ.mu0) / sZ)
            + θ.pN * InventoryControl.normalLoss ((aS + θ.mu0) / sZ)) := by
  intro Pr sZ aN aS
  obtain ⟨hpN0, hpN1, hsX, hn0, hc0, hdon, hIN, hIS, hzeta, hDel, hrho0, hrho1⟩ := hS
  have hPr : 0 ≤ Pr := by
    simp only [Pr, Prho]
    split_ifs with h
    · exact hP
    · have hρ : 0 < θ.rho := lt_of_le_of_ne hrho0 (Ne.symm h)
      apply mul_nonneg (div_nonneg hzeta.le hρ.le)
      rw [sub_nonneg, Real.exp_le_one_iff]
      have : 0 ≤ θ.rho * Ppop T / θ.zeta := div_nonneg (mul_nonneg hρ.le hP) hzeta.le
      have h2 : -θ.rho * Ppop T / θ.zeta = -(θ.rho * Ppop T / θ.zeta) := by ring
      linarith
  have hsZ : 0 < sZ := by
    simp only [sZ, sigZ]
    apply Real.sqrt_pos.mpr
    have hQ : 0 < T * r / 2 := by positivity
    positivity
  have hTr : T * r ≠ 0 := (mul_pos hT hr).ne'
  have hpost : postGain θ Pr (T * r / 2) = Pr * sZ *
      ((1 - θ.pN) * InventoryControl.normalLoss ((aN - θ.mu0) / sZ)
        + θ.pN * InventoryControl.normalLoss ((aS + θ.mu0) / sZ)) := by
    simp only [postGain]
    change ∫ z, (max (Pr * (1 - θ.pN) * z - θ.IN) 0 + max (-(Pr * θ.pN * z) - θ.IS) 0)
      ∂(gaussianReal θ.mu0 (sZ ^ 2).toNNReal) = _
    have hint2 : Integrable (fun z : ℝ => max (-(Pr * θ.pN * z) - θ.IS) 0)
        (gaussianReal θ.mu0 (sZ ^ 2).toNNReal) := by
      have := VBCT8.integrable_affine_pos θ.mu0 (sZ ^ 2).toNNReal (-(Pr * θ.pN)) θ.IS
      simpa [neg_mul] using this
    rw [integral_add (VBCT8.integrable_affine_pos _ _ _ _) hint2]
    have hA : ∫ z, max (Pr * (1 - θ.pN) * z - θ.IN) 0 ∂(gaussianReal θ.mu0 (sZ ^ 2).toNNReal)
        = Pr * sZ * (1 - θ.pN) * InventoryControl.normalLoss ((aN - θ.mu0) / sZ) := by
      rcases hPr.lt_or_eq with hPr' | hPr'
      · have ha : 0 < Pr * (1 - θ.pN) := mul_pos hPr' (by linarith)
        have : ∀ z, max (Pr * (1 - θ.pN) * z - θ.IN) 0
            = Pr * (1 - θ.pN) * max (z - aN) 0 := by
          intro z
          rw [mul_max_of_nonneg _ _ ha.le, mul_zero]
          congr 1
          simp only [aN]
          have h1 : (1 - θ.pN) ≠ 0 := by linarith
          have h2 : Pr ≠ 0 := hPr'.ne'
          field_simp
        simp_rw [this]
        rw [integral_const_mul, VBCT8.pos_part_gauss _ _ _ hsZ]
        ring
      · rw [← hPr']
        simp only [zero_mul, zero_sub, max_eq_right (neg_nonpos.mpr hIN), integral_zero]
    have hB : ∫ z, max (-(Pr * θ.pN * z) - θ.IS) 0 ∂(gaussianReal θ.mu0 (sZ ^ 2).toNNReal)
        = Pr * sZ * θ.pN * InventoryControl.normalLoss ((aS + θ.mu0) / sZ) := by
      rcases (mul_nonneg hPr hpN0).lt_or_eq with hb | hb
      · have : ∀ z, max (-(Pr * θ.pN * z) - θ.IS) 0
            = Pr * θ.pN * max (-z - aS) 0 := by
          intro z
          rw [mul_max_of_nonneg _ _ hb.le, mul_zero]
          congr 1
          simp only [aS]
          have h1 : θ.pN ≠ 0 := by rintro h; rw [h, mul_zero] at hb; exact lt_irrefl _ hb
          have h2 : Pr ≠ 0 := by rintro h; rw [h, zero_mul] at hb; exact lt_irrefl _ hb
          field_simp
        simp_rw [this]
        rw [integral_const_mul, VBCT8.neg_part_gauss _ _ _ hsZ]
        ring
      · have h0 : ∀ z, max (-(Pr * θ.pN * z) - θ.IS) 0 = 0 := by
          intro z; rw [← hb]; simp [max_eq_right (neg_nonpos.mpr hIS)]
        simp_rw [h0, integral_zero]
        rw [show Pr * sZ * θ.pN = (Pr * θ.pN) * sZ by ring, ← hb]; ring
    rw [hA, hB]; ring
  simp only [V, hTr, if_false]
  rw [hpost]
  ring
