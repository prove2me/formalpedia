-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flA_leviV_log_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:29:45.442589+00:00
-- url     : https://prove2.me/submissions/42fcb08b-0136-4176-affe-2c013939fdef

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_differentiableAt_wd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_of_differentiableAt
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_add
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_congr
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_conj
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wdb_of_differentiableAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {h : V n → ℂ} {y : V n}
    (hh : ∀ᶠ v in 𝓝 y, DifferentiableAt ℂ h v) (hne : h y ≠ 0) (ξ : Fin n → ℂ) :
    leviV n (fun v => ((Real.log (‖h v‖ ^ 2) : ℝ) : ℂ)) y ξ = 0 := by
  set Lf : V n → ℂ := fun v => Complex.log (h v / h y) with hLf
  have hcont : ContinuousAt (fun v => h v / h y) y :=
    (hh.self_of_nhds.continuousAt).div_const _
  have hslit : ∀ᶠ v in 𝓝 y, h v / h y ∈ Complex.slitPlane := by
    apply hcont.eventually_mem
    rw [div_self hne]
    exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
  have hLd : ∀ᶠ v in 𝓝 y, DifferentiableAt ℂ Lf v := by
    filter_upwards [hh, hslit] with v h1 h2
    have h3 : DifferentiableAt ℂ (fun v => h v / h y) v := by
      simpa [div_eq_mul_inv] using h1.mul_const (h y)⁻¹
    exact h3.clog h2
  obtain ⟨t, ht, hto, hyt⟩ := eventually_nhds_iff.mp hLd
  have hLc : ContDiffOn ℂ ∞ Lf t := contDiffOn_of_differentiableOn n Lf t hto
    (fun v hv => (ht v hv).differentiableWithinAt)
  have hL2 : ∀ v ∈ t, ContDiffAt ℂ 2 Lf v := fun v hv =>
    ((hLc v hv).contDiffAt (hto.mem_nhds hv)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hne' : ∀ᶠ v in 𝓝 y, h v ≠ 0 := hh.self_of_nhds.continuousAt.eventually_ne hne
  have hF : (fun v => ((Real.log (‖h v‖ ^ 2) : ℝ) : ℂ)) =ᶠ[𝓝 y]
      fun v => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ) + Lf v + conj (Lf v) := by
    filter_upwards [hne'] with v hv
    have h1 : Lf v + conj (Lf v) = ((2 * (Lf v).re : ℝ) : ℂ) := by
      rw [Complex.add_conj]
    rw [add_assoc, h1, Complex.log_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.mpr hv) (norm_ne_zero_iff.mpr hne), Real.log_pow,
      Real.log_pow]
    push_cast; try ring
  rw [leviV_congr hF]
  have hwdb : ∀ k, wdb n k (fun v => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ) + Lf v + conj (Lf v))
      =ᶠ[𝓝 y] fun v => conj (wd n k Lf v) := by
    intro k
    filter_upwards [hto.mem_nhds hyt] with v hv
    have hd : DifferentiableAt ℂ Lf v := ht v hv
    rw [wdb_add (f := fun v => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ) + Lf v) (g := fun v => conj (Lf v))
        ((differentiableAt_const _).add (hd.restrictScalars ℝ))
        (differentiableAt_conj (hd.restrictScalars ℝ)),
      wdb_add (f := fun _ => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ)) (g := Lf)
        (differentiableAt_const _) (hd.restrictScalars ℝ),
      wdb_conj (hd.restrictScalars ℝ), wdb_of_differentiableAt hd,
      wdb_of_differentiableAt (differentiableAt_const _)]
    ring
  have hz : ∀ j k, wd n j (wdb n k (fun v => ((Real.log (‖h y‖ ^ 2) : ℝ) : ℂ) + Lf v +
      conj (Lf v))) y = 0 := by
    intro j k
    have hwk : wd n k Lf =ᶠ[𝓝 y] fun v => fderiv ℂ Lf v (bas n k) := by
      filter_upwards [hto.mem_nhds hyt] with v hv
      exact wd_of_differentiableAt (ht v hv)
    have hdk : DifferentiableAt ℂ (fun v => fderiv ℂ Lf v (bas n k)) y :=
      (((hL2 y hyt).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
        (differentiableAt_const _)
    rw [wd_congr (hwdb k), wd_conj (differentiableAt_wd (hL2 y hyt |>.restrict_scalars ℝ)),
      wdb_congr hwk, wdb_of_differentiableAt hdk]
    simp
  simp only [leviV, hz, zero_mul, Finset.sum_const_zero]
end ReciprocityTheory.L2DbarEstimates.Y
