-- Prove2me | solution 2 for PetruzziDada.Additive.appendix_d2R
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:12:35.470182+00:00
-- url     : https://prove2.me/submissions/d6123983-fa98-4acb-8edf-f97fe912df26

import Mathlib
import Definitions.Def_PetruzziDada_Additive_Model
set_option autoImplicit false
open MeasureTheory PetruzziDada.Additive

namespace VVP
variable (M : Model)

noncomputable def Ii (w : ℝ) : ℝ := ∫ u in M.A..w, u * M.f u

lemma ii {a b : ℝ} (ha : a ∈ Set.Icc M.A M.B) (hb : b ∈ Set.Icc M.A M.B) :
    IntervalIntegrable M.f volume a b := by
  apply M.f_integrable.mono_set
  rw [Set.uIcc_of_le M.A_lt_B.le]
  exact Set.uIcc_subset_Icc ha hb

lemma ii2 {a b : ℝ} (ha : a ∈ Set.Icc M.A M.B) (hb : b ∈ Set.Icc M.A M.B) :
    IntervalIntegrable (fun u => u * M.f u) volume a b :=
  (ii M ha hb).continuousOn_mul (g := fun u => u) continuousOn_id

lemma mem_icc {z : ℝ} (hz : z ∈ Set.Icc M.A M.B) : M.A ∈ Set.Icc M.A M.B ∧ M.B ∈ Set.Icc M.A M.B :=
  ⟨⟨le_refl _, M.A_lt_B.le⟩, ⟨M.A_lt_B.le, le_refl _⟩⟩

lemma intf {z : ℝ} (hz : z ∈ Set.Icc M.A M.B) : ∫ u in z..M.B, M.f u = 1 - M.F z := by
  obtain ⟨hA, hB⟩ := mem_icc M hz
  have := intervalIntegral.integral_add_adjacent_intervals (ii M hA hz) (ii M hz hB)
  rw [M.f_total] at this
  unfold Model.F; linarith

lemma intg {z : ℝ} (hz : z ∈ Set.Icc M.A M.B) : ∫ u in z..M.B, u * M.f u = M.μ - Ii M z := by
  obtain ⟨hA, hB⟩ := mem_icc M hz
  have := intervalIntegral.integral_add_adjacent_intervals (ii2 M hA hz) (ii2 M hz hB)
  unfold Model.μ Ii; linarith

lemma Theta_eq {z : ℝ} (hz : z ∈ Set.Icc M.A M.B) : M.Θ z = M.μ - Ii M z - z * (1 - M.F z) := by
  obtain ⟨hA, hB⟩ := mem_icc M hz
  unfold Model.Θ
  have : (fun u => (u - z) * M.f u) = fun u => u * M.f u - z * M.f u := by funext u; ring
  rw [this, intervalIntegral.integral_sub (ii2 M hz hB) ((ii M hz hB).const_mul z),
    intervalIntegral.integral_const_mul, intg M hz, intf M hz]

lemma exp_eq {z : ℝ} (hz : z ∈ Set.Icc M.A M.B) (p : ℝ) :
    M.expProfit z p = (p * M.y p - M.h * z) * M.F z + (p + M.h) * Ii M z
      + (p * (M.y p + z) + M.s * z) * (1 - M.F z) - M.s * (M.μ - Ii M z) - M.c * (M.y p + z) := by
  obtain ⟨hA, hB⟩ := mem_icc M hz
  unfold Model.expProfit
  have e1 : (fun u => (p * (M.y p + u) - M.h * (z - u)) * M.f u)
      = fun u => (p * M.y p - M.h * z) * M.f u + (p + M.h) * (u * M.f u) := by funext u; ring
  have e2 : (fun u => (p * (M.y p + z) - M.s * (u - z)) * M.f u)
      = fun u => (p * (M.y p + z) + M.s * z) * M.f u - M.s * (u * M.f u) := by funext u; ring
  rw [e1, e2, intervalIntegral.integral_add ((ii M hA hz).const_mul _) ((ii2 M hA hz).const_mul _),
    intervalIntegral.integral_sub ((ii M hz hB).const_mul _) ((ii2 M hz hB).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intg M hz, intf M hz]
  unfold Model.F Ii
  ring


noncomputable def pr (w : ℝ) : ℝ := M.p0 - (M.μ - Ii M w - w * (1 - M.F w)) / (2 * M.b)

noncomputable def Ered (w : ℝ) : ℝ :=
  (pr M w * (M.a - M.b * pr M w) - M.h * w) * M.F w + (pr M w + M.h) * Ii M w
    + (pr M w * (M.a - M.b * pr M w + w) + M.s * w) * (1 - M.F w)
    - M.s * (M.μ - Ii M w) - M.c * (M.a - M.b * pr M w + w)

noncomputable def Rf (w : ℝ) : ℝ := (pr M w + M.s) * (1 - M.F w) - M.h * M.F w - M.c

noncomputable def R2 (w : ℝ) : ℝ := (1 - M.F w) ^ 2 / (2 * M.b) - (pr M w + (M.s + M.h)) * M.f w

lemma red_eq {w : ℝ} (hw : w ∈ Set.Icc M.A M.B) : M.reducedProfit w = Ered M w := by
  unfold Model.reducedProfit Ered
  have : M.price w = pr M w := by
    unfold Model.price pr; rw [Theta_eq M hw]
  rw [this, exp_eq M hw]
  unfold Model.y
  ring

lemma hdF (hf : DifferentiableOn ℝ M.f (Set.Ioo M.A M.B)) {w : ℝ} (hw : w ∈ Set.Ioo M.A M.B) :
    HasDerivAt M.F (M.f w) w := by
  have hc : ContinuousOn M.f (Set.Ioo M.A M.B) := hf.continuousOn
  have hca : ContinuousAt M.f w := hc.continuousAt (Ioo_mem_nhds hw.1 hw.2)
  have hm : StronglyMeasurableAtFilter M.f (nhds w) volume :=
    hc.stronglyMeasurableAtFilter isOpen_Ioo w hw
  exact intervalIntegral.integral_hasDerivAt_right (ii M ⟨le_refl _, M.A_lt_B.le⟩ ⟨hw.1.le, hw.2.le⟩) hm hca

lemma hdI (hf : DifferentiableOn ℝ M.f (Set.Ioo M.A M.B)) {w : ℝ} (hw : w ∈ Set.Ioo M.A M.B) :
    HasDerivAt (Ii M) (w * M.f w) w := by
  have hc : ContinuousOn (fun u => u * M.f u) (Set.Ioo M.A M.B) := continuousOn_id.mul hf.continuousOn
  have hca : ContinuousAt (fun u => u * M.f u) w := hc.continuousAt (Ioo_mem_nhds hw.1 hw.2)
  have hm : StronglyMeasurableAtFilter (fun u => u * M.f u) (nhds w) volume :=
    hc.stronglyMeasurableAtFilter isOpen_Ioo w hw
  exact intervalIntegral.integral_hasDerivAt_right (ii2 M ⟨le_refl _, M.A_lt_B.le⟩ ⟨hw.1.le, hw.2.le⟩) hm hca

lemma hdpr (hf : DifferentiableOn ℝ M.f (Set.Ioo M.A M.B)) {w : ℝ} (hw : w ∈ Set.Ioo M.A M.B) :
    HasDerivAt (pr M) ((1 - M.F w) / (2 * M.b)) w := by
  have hF := hdF M hf hw
  have hI := hdI M hf hw
  have hΘ := (hI.const_sub M.μ).sub ((hasDerivAt_id' w).mul (hF.const_sub 1))
  have := (hΘ.div_const (2 * M.b)).const_sub M.p0
  exact this.congr_deriv (by ring)

lemma hdE (hf : DifferentiableOn ℝ M.f (Set.Ioo M.A M.B)) {w : ℝ} (hw : w ∈ Set.Ioo M.A M.B) :
    HasDerivAt (Ered M) (Rf M w) w := by
  have hF := hdF M hf hw
  have hI := hdI M hf hw
  have hpr := hdpr M hf hw
  have hy := (hpr.const_mul M.b).const_sub M.a
  have t1 := ((hpr.mul hy).sub ((hasDerivAt_id' w).const_mul M.h)).mul hF
  have t2 := (hpr.add_const M.h).mul hI
  have t3 := ((hpr.mul (hy.add (hasDerivAt_id' w))).add ((hasDerivAt_id' w).const_mul M.s)).mul (hF.const_sub 1)
  have t4 := (hI.const_sub M.μ).const_mul M.s
  have t5 := (hy.add (hasDerivAt_id' w)).const_mul M.c
  have total := (((t1.add t2).add t3).sub t4).sub t5
  refine total.congr_deriv ?_
  have hb : M.b ≠ 0 := M.b_pos.ne'
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  unfold Rf pr Model.p0
  field_simp
  ring

lemma hdR (hf : DifferentiableOn ℝ M.f (Set.Ioo M.A M.B)) {w : ℝ} (hw : w ∈ Set.Ioo M.A M.B) :
    HasDerivAt (Rf M) (R2 M w) w := by
  have hF := hdF M hf hw
  have hpr := hdpr M hf hw
  have := (((hpr.add_const M.s).mul (hF.const_sub 1)).sub (hF.const_mul M.h)).sub_const M.c
  refine this.congr_deriv ?_
  unfold R2
  ring

lemma R_eq {w : ℝ} (hf : DifferentiableOn ℝ M.f (Set.Ioo M.A M.B)) (hw : w ∈ Set.Ioo M.A M.B) :
    M.R w = Rf M w := by
  have h1 : HasDerivAt M.reducedProfit (Rf M w) w := by
    apply (hdE M hf hw).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hw.1 hw.2] with x hx
    exact red_eq M ⟨hx.1.le, hx.2.le⟩
  exact h1.deriv

lemma dR_eq {w : ℝ} (hf : DifferentiableOn ℝ M.f (Set.Ioo M.A M.B)) (hw : w ∈ Set.Ioo M.A M.B) :
    deriv M.R w = R2 M w := by
  have h1 : HasDerivAt M.R (R2 M w) w := by
    apply (hdR M hf hw).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hw.1 hw.2] with x hx
    exact R_eq M hf hx
  exact h1.deriv

end VVP

theorem solution (M : Model) (hf : DifferentiableOn ℝ M.f (Set.Ioo M.A M.B))
    (z : ℝ) (hz : z ∈ Set.Ioo M.A M.B) (hfz : 0 < M.f z) (hcrit : deriv M.R z = 0) :
    HasDerivAt (deriv M.R)
      (-(M.f z * (1 - M.F z) / (2 * M.b * M.hazard z ^ 2)) *
        (2 * M.hazard z ^ 2 + deriv M.hazard z)) z := by
  have hF := VVP.hdF M hf hz
  have hpr := VVP.hdpr M hf hz
  have hfd : HasDerivAt M.f (deriv M.f z) z :=
    ((hf z hz).differentiableAt (Ioo_mem_nhds hz.1 hz.2)).hasDerivAt
  have hb : M.b ≠ 0 := M.b_pos.ne'
  have hR2 : HasDerivAt (VVP.R2 M)
      ((2 * (1 - M.F z) * (-M.f z)) / (2 * M.b)
        - ((1 - M.F z) / (2 * M.b) * M.f z + (VVP.pr M z + (M.s + M.h)) * deriv M.f z)) z := by
    have := (((hF.const_sub 1).pow 2).div_const (2 * M.b)).sub
      ((hpr.add_const (M.s + M.h)).mul hfd)
    refine this.congr_deriv ?_
    simp
  have hev : deriv M.R =ᶠ[nhds z] VVP.R2 M := by
    filter_upwards [Ioo_mem_nhds hz.1 hz.2] with x hx
    exact VVP.dR_eq M hf hx
  have hD := hR2.congr_of_eventuallyEq hev
  have hc : VVP.R2 M z = 0 := by rw [← VVP.dR_eq M hf hz]; exact hcrit
  unfold VVP.R2 at hc
  suffices key : (-(M.f z * (1 - M.F z) / (2 * M.b * M.hazard z ^ 2)) *
        (2 * M.hazard z ^ 2 + deriv M.hazard z)) =
      (2 * (1 - M.F z) * (-M.f z)) / (2 * M.b)
        - ((1 - M.F z) / (2 * M.b) * M.f z + (VVP.pr M z + (M.s + M.h)) * deriv M.f z) by
    rw [key]; exact hD
  by_cases he : 1 - M.F z = 0
  · rw [he] at hc ⊢
    have h0 : (0:ℝ) ^ 2 / (2 * M.b) = 0 := by simp
    rw [h0] at hc
    have hP : VVP.pr M z + (M.s + M.h) = 0 := by
      have : (VVP.pr M z + (M.s + M.h)) * M.f z = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hfz.ne'
    rw [hP]; simp
  · have hh : HasDerivAt M.hazard ((deriv M.f z * (1 - M.F z) - M.f z * (-M.f z)) / (1 - M.F z) ^ 2) z :=
      hfd.div (hF.const_sub 1) he
    rw [hh.deriv]
    have hP : VVP.pr M z + (M.s + M.h) = (1 - M.F z) ^ 2 / (2 * M.b * M.f z) := by
      field_simp
      field_simp at hc
      linarith
    rw [hP]
    unfold Model.hazard
    have hf0 : M.f z ≠ 0 := hfz.ne'
    field_simp
    ring
