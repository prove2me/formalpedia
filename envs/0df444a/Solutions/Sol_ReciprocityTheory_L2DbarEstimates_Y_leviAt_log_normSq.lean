-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.leviAt_log_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:23:47.756099+00:00
-- url     : https://prove2.me/submissions/03d6288a-e0b0-4a7e-bb93-955b234d09d6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatCalc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_holoDeriv
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_of_differentiableAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_ofReal_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_of_differentiableAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La) (i : ι) (h : Y → ℂ) (y : Y) (hy : y ∈ (A.chart i).source)
    (hh : ∀ᶠ v in 𝓝 (A.chart i y), DifferentiableAt ℂ (h ∘ (A.chart i).symm) v)
    (hne : h y ≠ 0) (ξ : Fin n → ℂ) :
    A.leviAt i (fun x => Real.log (‖h x‖ ^ 2)) y ξ = 0 := by

  have hp0 : h ((A.chart i).symm (A.chart i y)) ≠ 0 := by rw [(A.chart i).left_inv hy]; exact hne
  have hH' : ∀ᶠ v in 𝓝 (A.chart i y), DifferentiableAt ℂ (fun v => h ((A.chart i).symm v)) v := hh
  obtain ⟨t, ht, hto, hpt⟩ := eventually_nhds_iff.1 hH'
  have hHt : DifferentiableOn ℂ (fun v => h ((A.chart i).symm v)) t :=
    fun v hv => (ht v hv).differentiableWithinAt
  have hne' : ∀ᶠ v in 𝓝 (A.chart i y), h ((A.chart i).symm v) ≠ 0 :=
    (hH'.self_of_nhds).continuousAt.eventually_ne hp0
  have key : ∀ j k, wd n j (wdb n k (fun v => ((Real.log (‖h ((A.chart i).symm v)‖ ^ 2) : ℝ) : ℂ)))
      (A.chart i y) = 0 := by
    intro j k
    have hQd : DifferentiableAt ℂ (fun v => fderiv ℂ (fun v => h ((A.chart i).symm v)) v (bas n k) *
        (h ((A.chart i).symm v))⁻¹) (A.chart i y) :=
      ((ReciprocityTheory.L2DbarEstimates.C.holoDeriv n t _ hto hHt (bas n k)).differentiableAt (hto.mem_nhds hpt)).mul
        ((hH'.self_of_nhds).inv hp0)
    have hev : wdb n k (fun v => ((Real.log (‖h ((A.chart i).symm v)‖ ^ 2) : ℝ) : ℂ)) =ᶠ[𝓝 (A.chart i y)]
        fun v => (starRingEnd ℂ) (fderiv ℂ (fun v => h ((A.chart i).symm v)) v (bas n k) *
          (h ((A.chart i).symm v))⁻¹) := by
      filter_upwards [hto.mem_nhds hpt, hne'] with v hvt hv0
      have hd : DifferentiableAt ℂ (fun v => h ((A.chart i).symm v)) v := ht v hvt
      have hdR := hd.restrictScalars ℝ
      have hN : ‖h ((A.chart i).symm v)‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hv0)
      rw [wdb_ofReal_comp (k := Real.log) (v := fun v => ‖h ((A.chart i).symm v)‖ ^ 2)
        (Real.differentiableAt_log hN) (by first | exact DifferentiableAt.norm_sq ℝ hdR | exact hdR.norm_sq (𝕜 := ℝ) | exact hdR.norm_sq ℂ)]
      have hsq : (fun y => (((‖h ((A.chart i).symm y)‖ ^ 2 : ℝ)) : ℂ)) =
          fun y => h ((A.chart i).symm y) * (starRingEnd ℂ) (h ((A.chart i).symm y)) := by
        funext y
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
        try push_cast
        try ring
      have hcR : DifferentiableAt ℝ (fun y => (starRingEnd ℂ) (h ((A.chart i).symm y))) v :=
        Complex.conjCLE.differentiable.differentiableAt.comp v hdR
      have hc : ((‖h ((A.chart i).symm v)‖ ^ 2 : ℝ) : ℂ) =
          h ((A.chart i).symm v) * (starRingEnd ℂ) (h ((A.chart i).symm v)) := congrFun hsq v
      have hca : (starRingEnd ℂ) (h ((A.chart i).symm v)) ≠ 0 := (map_ne_zero _).2 hv0
      rw [hsq, wdb_mul hdR hcR, wdb_of_differentiableAt hd, wdb_conj hdR, wd_of_differentiableAt hd]
      simp only [Real.deriv_log, Complex.ofReal_inv, hc, map_mul, map_inv₀]
      field_simp
      ring
    rw [wd_congr hev, wd_conj (hQd.restrictScalars ℝ), wdb_of_differentiableAt hQd, map_zero]
  unfold WeightedAtlas.leviAt leviV
  simp only [key, zero_mul, Finset.sum_const_zero, Complex.zero_re]
end ReciprocityTheory.L2DbarEstimates.Y
