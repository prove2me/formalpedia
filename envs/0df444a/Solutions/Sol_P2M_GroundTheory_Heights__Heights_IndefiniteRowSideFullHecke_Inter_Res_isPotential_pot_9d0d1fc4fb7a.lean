-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_isPotential_pot_9d0d1fc4fb7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:03:46.641725+00:00
-- url     : https://prove2.me/submissions/3d449795-0a38-49f2-b3e4-6b138f214556

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_liftAt_mem_61d8fb3d277f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_sameOrbit_liftAt_1a859d9855f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_continuousOn_liftAt_90ad233d8615
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_analyticAt_liftAt_b90f8c15a691
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_analyticAt_liftAt_pi_7b40b5bddbb5
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial MeasureTheory Topology Filter Set
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential MIntegrable locDens)
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res
variable {P : Ideal (MRing ι ℂ)} {e : ℕ} (R : Res ι P e)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res
theorem _root_.solution {φ : MCone ι → ℝ} (hφ : IsSmoothPot P φ) :
    IsPotential R.atlas (R.pot φ) := by
  classical
  obtain ⟨⟨a, ha⟩, hloc⟩ := hφ
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  ·
    intro u hu
    have hu' : u ∈ (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x) := hu
    have hγ : AnalyticAt ℂ (fun v => R.liftAt x ((R.atlas.chart j).symm v)) u :=
      R.analyticAt_liftAt_pi x j hu'
    obtain ⟨U, hU, G, hG, hGφ⟩ := hloc _ (R.liftAt_mem hu'.2)
    have hGc : ContDiffAt ℝ ∞ (G ∘ fun v => R.liftAt x ((R.atlas.chart j).symm v)) u :=
      (hG.contDiffAt hU).comp u ((hγ.contDiffAt (n := ∞)).restrict_scalars ℝ)
    refine hGc.contDiffWithinAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (hγ.continuousAt.preimage_mem_nhds hU)] with v hv hvU
      exact hGφ _ ⟨hvU, R.liftAt_mem hv.2⟩
    · exact hGφ _ ⟨mem_of_mem_nhds hU, R.liftAt_mem hu'.2⟩
  ·
    have hy' : y ∈ R.R.src (R.idx x) ∩ R.R.src (R.idx x') := hy
    choose p hp using (R.liftAt_mem hy'.2).1
    obtain ⟨c, hc, hcy⟩ := R.sameOrbit_liftAt hy'.1 hy'.2
    have hnum : ∀ k, R.liftAt x y ⟨k, p k⟩ ≠ 0 := fun k => by
      rw [hcy]; exact mul_ne_zero (hc k) (hp k)
    have hr : ∀ k, R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩ ≠ 0 :=
      fun k => div_ne_zero (hnum k) (hp k)
    have hO : IsOpen (R.R.src (R.idx x) ∩ R.R.src (R.idx x')) :=
      (R.R.isOpen_alt_bis _).inter (R.R.isOpen_alt_bis _)
    let q : K → R.R.M → ℂ := fun k z => R.liftAt x z ⟨k, p k⟩ / R.liftAt x' z ⟨k, p k⟩ /
      (R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩)
    let W : Set R.R.M := {z | z ∈ R.R.src (R.idx x) ∩ R.R.src (R.idx x') ∧
      ∀ k, R.liftAt x' z ⟨k, p k⟩ ≠ 0 ∧ q k z ∈ Complex.slitPlane}
    have hW : IsOpen W := by
      refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
      have hn : ∀ k, ContinuousAt (fun z => R.liftAt x z ⟨k, p k⟩) z := fun k =>
        ((R.continuousOn_liftAt x _).mono inter_subset_left).continuousAt (hO.mem_nhds hz.1)
      have hd : ∀ k, ContinuousAt (fun z => R.liftAt x' z ⟨k, p k⟩) z := fun k =>
        ((R.continuousOn_liftAt x' _).mono inter_subset_right).continuousAt (hO.mem_nhds hz.1)
      filter_upwards [hO.mem_nhds hz.1, eventually_all.mpr fun k => (hd k).eventually_ne (hz.2 k).1,
        eventually_all.mpr fun k => (((hn k).div (hd k) (hz.2 k).1).div_const _).eventually_mem
          (Complex.isOpen_slitPlane.mem_nhds (hz.2 k).2)] with w h1 h2 h3
      exact ⟨h1, fun k => ⟨h2 k, h3 k⟩⟩
    have hyW : y ∈ W := by
      refine ⟨hy', fun k => ⟨hp k, ?_⟩⟩
      have : q k y = 1 := div_self (hr k)
      rw [this]
      exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
    let G : R.R.M → ℂ := fun z => ∑ k, ((a k : ℝ) : ℂ) *
      (Complex.log (q k z) + ((Real.log ‖R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩‖ : ℝ) : ℂ))
    refine ⟨W, hW, hyW, G, fun j y' hy'' => ?_, fun z hz => ?_⟩
    ·
      have hz : (R.atlas.chart j).symm y' ∈ W := hy''.2
      have hterm : ∀ k, AnalyticAt ℂ (fun y'' => ((a k : ℝ) : ℂ) *
          (Complex.log (q k ((R.atlas.chart j).symm y'')) +
            ((Real.log ‖R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩‖ : ℝ) : ℂ))) y' := by
        intro k
        have hn : AnalyticAt ℂ (fun y'' => R.liftAt x ((R.atlas.chart j).symm y'') ⟨k, p k⟩) y' :=
          R.analyticAt_liftAt x _ j ⟨hy''.1, hz.1.1⟩
        have hd : AnalyticAt ℂ (fun y'' => R.liftAt x' ((R.atlas.chart j).symm y'') ⟨k, p k⟩) y' :=
          R.analyticAt_liftAt x' _ j ⟨hy''.1, hz.1.2⟩
        have hq : AnalyticAt ℂ (fun y'' => q k ((R.atlas.chart j).symm y'')) y' :=
          (hn.div hd (hz.2 k).1).div analyticAt_const (hr k)
        have hl : AnalyticAt ℂ (Complex.log ∘ fun y'' => q k ((R.atlas.chart j).symm y'')) y' :=
          AnalyticAt.comp (f := fun y'' => q k ((R.atlas.chart j).symm y''))
            (analyticAt_clog (hz.2 k).2) hq
        exact analyticAt_const.mul (hl.add analyticAt_const)
      exact Finset.analyticAt_fun_sum _ fun k _ => hterm k
    ·
      have hzW : z ∈ W := hz.1.1
      obtain ⟨c', hc', hcz⟩ := R.sameOrbit_liftAt hzW.1.1 hzW.1.2
      have hterm : ∀ k, Real.log ‖q k z‖ +
          Real.log ‖R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩‖ = Real.log ‖c' k‖ := by
        intro k
        have hqz : q k z = c' k / (R.liftAt x y ⟨k, p k⟩ / R.liftAt x' y ⟨k, p k⟩) := by
          simp only [q]
          rw [hcz]
          simp only [tsmul]
          rw [mul_div_assoc, div_self (hzW.2 k).1, mul_one]
        rw [hqz, norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k))
          (norm_ne_zero_iff.mpr (hr k))]
        ring
      show φ (R.liftAt x z) - φ (R.liftAt x' z) = (G z).re
      rw [hcz, ha c' hc' _ (R.liftAt_mem hzW.1.2), add_sub_cancel_left]
      simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.add_re, Complex.log_re,
        Complex.ofReal_re]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm k]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res
