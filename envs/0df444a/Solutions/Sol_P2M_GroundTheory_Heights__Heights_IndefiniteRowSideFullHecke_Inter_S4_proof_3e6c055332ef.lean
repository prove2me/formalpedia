-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_S4_proof_3e6c055332ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:11:24.532692+00:00
-- url     : https://prove2.me/submissions/bb86c887-5ebd-411a-955c-38c3587edfae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AnalyticResolutionHypothesesProjectiveLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FourierIntegralBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_secNorm_tsmul_fa0d9ccb09f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_abs_log_div_le__78ed9d7353d4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_liftAt_mem_61d8fb3d277f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_sameOrbit_liftAt_1a859d9855f3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_analyticAt_liftAt_pi_7b40b5bddbb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_Res_isPotential_pot_9d0d1fc4fb7a
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_logAbsLocInt__55b1400e9a63
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
import Theorems.Thm_ReciprocityTheory_AnForm_R_analyticAt_eval_of_pi
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace S4
theorem _root_.solution : S4.Statement := by
  intro K _ _ ι _ P e R φ A s _ hφ hA hs j Kc hK hKc
  refine LocallyIntegrableOn.integrableOn_compact_subset ?_ hK hKc
  intro u0 hu0
  set x0 := (R.atlas.chart j).symm u0
  set V := (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x0) with hVdef
  have hV : IsOpen V := (R.atlas.chart j).isOpen_inter_preimage_symm (R.R.isOpen_alt_bis _)
  have hu0V : u0 ∈ V := ⟨hu0, R.mem_src_idx x0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 hu0V
  set B := Metric.closedBall u0 (r / 2) with hBdef
  have hBV : B ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  refine ⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  set γ : (Fin e → ℂ) → MCone ι := fun u => R.liftAt x0 ((R.atlas.chart j).symm u) with hγdef
  have hγ : ∀ u ∈ V, AnalyticAt ℂ γ u := fun u hu => R.analyticAt_liftAt_pi x0 j hu
  have hγZ : ∀ u ∈ V, γ u ∈ zPts P := fun u hu => R.liftAt_mem hu.2
  set f : (Fin e → ℂ) → ℂ := fun u => eval (γ u) s with hfdef
  have hf : AnalyticOnNhd ℂ f V := fun u hu =>
    ReciprocityTheory.AnForm.R.analyticAt_eval_of_pi (fun q => analyticAt_pi_iff.mp (hγ u hu) q) s
  set H : (Fin e → ℂ) → ℝ := fun u => A.h (γ u) with hHdef
  have hHpos : ∀ u ∈ V, 0 < H u := fun u hu => A.pos _ (hγZ u hu).1
  have hHc : ContinuousOn H V := by
    intro u hu
    obtain ⟨U, hU, G, hG, hGe⟩ := hA (γ u) (hγZ u hu)
    have hcont : ContinuousAt (fun u' => Real.exp (G (γ u'))) u :=
      Real.continuous_exp.continuousAt.comp
        ((hG.continuousOn.continuousAt hU).comp (hγ u hu).continuousAt)
    refine (hcont.congr ?_).continuousWithinAt
    filter_upwards [hV.mem_nhds hu, (hγ u hu).continuousAt.preimage_mem_nhds hU] with v hv hvU
    show Real.exp (G (γ v)) = A.h (γ v)
    rw [← hGe _ ⟨hvU, hγZ v hv⟩]
    exact Real.exp_log (hHpos v hv)
  have hF : ∀ u ∈ V, secNorm A s (R.pt ((R.atlas.chart j).symm u)) = Real.log (‖f u‖ / H u) := by
    intro u hu
    obtain ⟨c, hc, hcz⟩ := R.sameOrbit_liftAt (x := (R.atlas.chart j).symm u) (x' := x0)
      (R.mem_src_idx _) hu.2
    show secNorm A s (R.liftAt _ _) = _
    rw [hcz, secNorm_tsmul hs hc]
    rfl
  have hDc : ContinuousOn (locDens R.atlas (fun i => R.pot (φ i)) j) B :=
    (ReciprocityTheory.AnForm.M.locDensCont R.atlas _ (fun i => R.isPotential_pot (hφ i)) j).mono
      (hBV.trans inter_subset_left)
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hDc
  have hlogf : IntegrableOn (fun u => Real.log ‖f u‖) B :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt' e V f hV hf).integrableOn_compact_subset hBV hBc
  have hlogH : IntegrableOn (fun u => Real.log (H u)) B :=
    ((hHc.mono hBV).log fun u hu => (hHpos u (hBV hu)).ne').integrableOn_compact hBc
  have hfc : ContinuousOn f B := fun u hu => (hf u (hBV hu)).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun u => Real.log (‖f u‖ / H u) *
      locDens R.atlas (fun i => R.pot (φ i)) j u) (volume.restrict B) := by
    have h1 : AEStronglyMeasurable (fun u => ‖f u‖ / H u) (volume.restrict B) :=
      (hfc.norm.div (hHc.mono hBV) fun u hu => (hHpos u (hBV hu)).ne').aestronglyMeasurable hBm
    exact (Real.measurable_log.comp_aemeasurable h1.aemeasurable).aestronglyMeasurable.mul
      (hDc.aestronglyMeasurable hBm)
  have hint : IntegrableOn (fun u => Real.log (‖f u‖ / H u) *
      locDens R.atlas (fun i => R.pot (φ i)) j u) B := by
    refine Integrable.mono' ((hlogf.norm.add hlogH.norm).mul_const M) hmeas ?_
    refine ae_restrict_of_forall_mem hBm fun u hu => ?_
    rw [norm_mul]
    have hb := abs_log_div_le' (norm_nonneg (f u)) (hHpos u (hBV hu))
    simp only [Real.norm_eq_abs] at hb ⊢
    exact mul_le_mul hb (hM u hu) (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine hint.congr_fun (fun u hu => ?_) hBm
  simp only
  rw [hF u (hBV hu)]
end S4
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
