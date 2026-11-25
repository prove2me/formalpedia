-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.logNormIntegrable_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:14:47.6478+00:00
-- url     : https://prove2.me/submissions/3e930c67-f94b-43ad-9c73-b1eb7c27db93

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LogInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LogInt
import Theorems.Thm_ReciprocityTheory_AnForm_M_logNormSec_eq_indicator
import Theorems.Thm_ReciprocityTheory_AnForm_M_prod_option_eq_prod_zpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (hLU : ReciprocityTheory.AnForm.A.LogUnitMonoLocIntStatement)
    (hD : LocDensContStatement) : LogNormIntegrableStatement := by
  intro e X _ _ _ A L s r m W hL hS hSNC Φ hΦ j K hKt hK
  refine LocallyIntegrableOn.integrableOn_isCompact (fun y0 hy0 => ?_) hK
  set c := A.chart j with hc
  have hy0t : y0 ∈ c.target := hKt hy0
  obtain ⟨ψ, hψc, hx0ψ, hψU, σ, -, -, u, hu, hu0, hsu⟩ := hSNC (c.symm y0)
  set x0 := c.symm y0 with hx0
  have hNo : IsOpen (c.target ∩ c.symm ⁻¹' ψ.source) := c.isOpen_inter_preimage_symm ψ.open_source
  have hy0N : y0 ∈ c.target ∩ c.symm ⁻¹' ψ.source := ⟨hy0t, hx0ψ⟩
  obtain ⟨ε, hε, hεN⟩ := Metric.isOpen_iff.mp hNo y0 hy0N
  set B := Metric.closedBall y0 (ε / 2) with hB
  have hBN : B ⊆ c.target ∩ c.symm ⁻¹' ψ.source :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεN
  have hBc : IsCompact B := isCompact_closedBall y0 (ε / 2)
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  refine ⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds y0 (by linarith)), ?_⟩

  set V := ψ.target ∩ ψ.symm ⁻¹' c.source with hV
  have hVo : IsOpen V := ψ.isOpen_inter_preimage_symm c.open_source
  have hTinvA : AnalyticOnNhd ℂ (c ∘ ψ.symm) V := (hψc j).2
  have hTV : ∀ y ∈ c.target ∩ c.symm ⁻¹' ψ.source,
      ψ (c.symm y) ∈ V ∧ c (ψ.symm (ψ (c.symm y))) = y := by
    intro y hy
    refine ⟨⟨ψ.map_source hy.2, ?_⟩, ?_⟩
    · simp only [Set.mem_preimage, ψ.left_inv hy.2]
      exact c.map_target hy.1
    · rw [ψ.left_inv hy.2, c.right_inv hy.1]

  set m' : Fin e → ℤ :=
    fun i => ((∑ k ∈ Finset.univ.filter (fun k => σ k = some i), m k : ℕ) : ℤ) with hm'
  set G : (Fin e → ℂ) → ℝ := fun z => Real.log ‖u (ψ.symm z) * ∏ i, z i ^ m' i‖ with hG
  have hGloc : LocallyIntegrableOn G V := by
    refine hLU e m' V (fun z => u (ψ.symm z)) hVo ?_ (fun z hz => hu0 _ (ψ.map_target hz.1))
    intro z hz
    have hw : c (ψ.symm z) ∈ c.target ∩ c.symm ⁻¹' ψ.source := by
      refine ⟨c.map_source hz.2, ?_⟩
      simp only [Set.mem_preimage, c.left_inv hz.2]
      exact ψ.map_target hz.1
    have h1 : AnalyticAt ℂ ((u ∘ c.symm) ∘ (c ∘ ψ.symm)) z :=
      AnalyticAt.comp (g := u ∘ c.symm) (f := c ∘ ψ.symm) (hu j _ hw) (hTinvA z hz)
    refine (h1.differentiableAt.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hVo.mem_nhds hz] with w hw
    simp [Function.comp, c.left_inv hw.2]

  have hTc : ContinuousOn (fun y => ψ (c.symm y)) (c.target ∩ c.symm ⁻¹' ψ.source) :=
    ψ.continuousOn.comp (c.continuousOn_symm.mono Set.inter_subset_left) (fun y hy => hy.2)
  set C := (fun y => ψ (c.symm y)) '' B with hC
  have hCc : IsCompact C := hBc.image_of_continuousOn (hTc.mono hBN)
  have hCm : MeasurableSet C := hCc.isClosed.measurableSet
  have hCV : C ⊆ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hTV y (hBN hy)).1
  have hCB : (c ∘ ψ.symm) '' C = B := by
    rw [hC, Set.image_image]
    conv_rhs => rw [← Set.image_id B]
    exact Set.image_congr fun y hy => (hTV y (hBN hy)).2
  have hinj : Set.InjOn (c ∘ ψ.symm) C := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ h
    simp only [Function.comp_apply] at h
    rw [(hTV y (hBN hy)).2, (hTV y' (hBN hy')).2] at h
    rw [h]
  have hderR : ∀ z ∈ V, DifferentiableAt ℝ (c ∘ ψ.symm) z := fun z hz =>
    (hTinvA z hz).differentiableAt.restrictScalars ℝ
  have hdetc : ContinuousOn (fun z => |(fderiv ℝ (c ∘ ψ.symm) z).det|) C := by
    have h1 : ContDiffOn ℝ 1 (c ∘ ψ.symm) V :=
      (hTinvA.contDiffOn_of_completeSpace (n := 1)).restrict_scalars ℝ
    exact ((ContinuousLinearMap.continuous_det.comp_continuousOn
      (h1.continuousOn_fderiv_of_isOpen hVo le_rfl)).abs).mono hCV
  have hGT : IntegrableOn (fun y => G (ψ (c.symm y))) B := by
    have hiff := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)
      hCm (f := c ∘ ψ.symm) (f' := fun z => fderiv ℝ (c ∘ ψ.symm) z)
      (fun z hz => (hderR z (hCV hz)).hasFDerivAt.hasFDerivWithinAt) hinj
      (fun y => G (ψ (c.symm y)))
    rw [hCB] at hiff
    refine hiff.mpr ?_
    refine IntegrableOn.congr_fun
      ((hGloc.integrableOn_compact_subset hCV hCc).continuousOn_smul hdetc hCc) ?_ hCm
    rintro _ ⟨y, hy, rfl⟩
    have h := (hTV y (hBN hy)).2
    simp only [Function.comp_apply, h]

  have hdB : ContinuousOn (locDens A Φ j) B :=
    (hD A Φ hΦ j).mono (hBN.trans Set.inter_subset_left)
  have hsub : c.target ∩ c.symm ⁻¹' ψ.source ⊆ c.target ∩ c.symm ⁻¹' L.U x0 :=
    fun y hy => ⟨hy.1, hψU hy.2⟩
  have hφB : ContinuousOn (fun y => L.φ x0 (c.symm y)) B :=
    ((hL.1 x0 j).continuousOn.mono hsub).mono hBN
  have hsB : ContinuousOn (fun y => s x0 (c.symm y)) B :=
    ((hS.1 x0 j).continuousOn.mono hsub).mono hBN
  set Z := B ∩ (fun y => s x0 (c.symm y)) ⁻¹' {0} with hZ
  have hZm : MeasurableSet Z :=
    (hsB.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_singleton).measurableSet
  have h1 : IntegrableOn (fun y => G (ψ (c.symm y)) * locDens A Φ j y) B :=
    hGT.mul_continuousOn hdB hBc
  have h2 : IntegrableOn (fun y => L.φ x0 (c.symm y) * locDens A Φ j y) B :=
    (hφB.mul hdB).integrableOn_compact hBc
  have h3 := h2.indicator hZm
  refine IntegrableOn.congr_fun (Integrable.add (Integrable.sub h1 h2) h3) ?_ hBm
  intro y hy
  have hyN := hBN hy
  have hp : c.symm y ∈ L.U x0 := hψU hyN.2
  have hprod : ∀ w : Fin e → ℂ, (∏ k, (match σ k with
      | some i => w i ^ m k
      | none => 1)) = ∏ i, w i ^ m' i := by
    intro w
    apply prod_option_eq_prod_zpow
    intro k
    split <;> simp_all
  have hlog : Real.log ‖s x0 (c.symm y)‖ = G (ψ (c.symm y)) := by
    show _ = Real.log ‖u (ψ.symm (ψ (c.symm y))) * ∏ i, (ψ (c.symm y)) i ^ m' i‖
    rw [ψ.left_inv hyN.2, hsu _ hyN.2]
    exact congrArg (fun t => Real.log ‖u (c.symm y) * t‖) (hprod _)
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [logNormSec_eq_indicator hS hp, hlog]
  by_cases h0 : s x0 (c.symm y) = 0
  · rw [Set.indicator_of_mem (show y ∈ Z from ⟨hy, h0⟩),
      Set.indicator_of_mem (show c.symm y ∈ {q | s x0 q = 0} from h0)]
    ring
  · rw [Set.indicator_of_notMem (show y ∉ Z from fun h => h0 h.2),
      Set.indicator_of_notMem (show c.symm y ∉ {q | s x0 q = 0} from h0)]
    ring
end ReciprocityTheory.AnForm.M
