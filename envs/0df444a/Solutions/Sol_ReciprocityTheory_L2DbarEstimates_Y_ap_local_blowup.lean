-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ap_local_blowup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:30:59.730733+00:00
-- url     : https://prove2.me/submissions/f55d9660-e582-4f95-adf1-155744aab2cb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeB
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_APrimeLoc
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_ap_prod_blowup
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_aprb_complement
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_aprb_contDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
private lemma exists_const_lintegral_comp_continuousLinearEquiv {n a b : ℕ} (A : V n ≃L[ℂ] V a × V b) :
    ∃ K : NNReal, 0 < K ∧ ∀ (B : Set (V a × V b)) (h : V n → ℝ≥0∞),
      ∫⁻ z in B, h (A.symm z) = (K : ℝ≥0∞) * ∫⁻ x in (A : V n → V a × V b) ⁻¹' B, h x := by
  haveI hvolF : (volume : Measure (V a × V b)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    haveI : (volume : Measure (V a)).IsAddHaarMeasure := inferInstance
    haveI : (volume : Measure (V b)).IsAddHaarMeasure := inferInstance
    haveI : SigmaFinite (volume : Measure (V a)) := inferInstance
    haveI : SigmaFinite (volume : Measure (V b)) := inferInstance
    first
      | infer_instance
      | exact Measure.prod.instIsAddHaarMeasure _ _
      | exact
          { toIsFiniteMeasureOnCompacts := inferInstance
            toIsAddLeftInvariant := inferInstance
            toIsOpenPosMeasure := inferInstance }
  set ν : Measure (V n) := Measure.map (A.symm : V a × V b → V n) volume with hν
  haveI : ν.IsAddHaarMeasure := by
    rw [hν]
    first
      | infer_instance
      | exact A.symm.isAddHaarMeasure_map volume
      | exact ContinuousLinearEquiv.isAddHaarMeasure_map A.symm volume
      | exact Measure.MapContinuousLinearEquiv.isAddHaarMeasure volume A.symm
      | exact (A.symm.restrictScalars ℝ).isAddHaarMeasure_map volume
      | exact Measure.isAddHaarMeasure_map volume
          (A.symm : V a × V b →+ V n) A.symm.continuous A.symm.surjective
          (A.symm.toHomeomorph.toCocompactMap.cocompact_tendsto')
  refine ⟨Measure.addHaarScalarFactor ν volume,
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume, ?_⟩
  intro B h
  have hmp : MeasurePreserving (A.symm : V a × V b → V n) volume ν :=
    ⟨A.symm.continuous.measurable, rfl⟩
  have hemb : MeasurableEmbedding (A.symm : V a × V b → V n) :=
    A.symm.toHomeomorph.measurableEmbedding
  have hpre : (A.symm : V a × V b → V n) ⁻¹' ((A : V n → V a × V b) ⁻¹' B) = B := by
    ext z; simp
  have key := hmp.setLIntegral_comp_preimage_emb hemb h ((A : V n → V a × V b) ⁻¹' B)
  rw [hpre] at key
  rw [key]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ν volume]
  rw [Measure.restrict_smul, lintegral_smul_measure]
  first
    | rfl
    | simp [ENNReal.smul_def]
end
end ReciprocityTheory.L2DbarEstimates.Y
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal
noncomputable section
set_option maxHeartbeats 800000
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (n d : ℕ) (hd : 1 ≤ d) (hMVd : ∀ k, MVStatement k)
    (hMVI : MVIntStatement d) (U : Set (V n)) (hU : IsOpen U) (p : V n → V d)
    (hp : DifferentiableOn ℂ p U) (v0 : V n) (hv0 : v0 ∈ U) (hp0 : p v0 = 0)
    (hsurj : Function.Surjective (fderiv ℂ p v0)) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.closedBall v0 δ ⊆ U ∧ ∀ M : ℝ, ∃ τ0 : ℝ, 0 < τ0 ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ τ0 → ∀ u : V n → ℂ, DifferentiableOn ℂ u (Metric.ball v0 δ) →
        ENNReal.ofReal (M * ‖u v0‖ ^ 2) ≤
          ∫⁻ v in Metric.ball v0 δ, ENNReal.ofReal (‖u v‖ ^ 2 * (max (‖p v‖ ^ 2) τ) ^ (-(d : ℝ))) := by
  classical
  obtain ⟨A, hA⟩ := aprb_complement (fderiv ℂ p v0) hsurj
  obtain ⟨K, hK, hKeq⟩ := exists_const_lintegral_comp_continuousLinearEquiv A
  set Lsnd : V n →L[ℂ] V (n - d) :=
    (ContinuousLinearMap.snd ℂ (V d) (V (n - d))).comp (A : V n →L[ℂ] V d × V (n - d)) with hLsnd
  set Ψ : V n → V n := fun v => A.symm (p v, Lsnd v - Lsnd v0) with hΨdef
  have hΨ0 : Ψ v0 = 0 := by simp [Ψ, hp0]
  have hpC : ContDiffOn ℂ 1 p U := by simpa using aprb_contDiffOn hU hp 1
  have hΨdiff : ∀ v ∈ U, DifferentiableAt ℂ Ψ v := by
    intro v hv
    have h1 : DifferentiableAt ℂ p v := hp.differentiableAt (hU.mem_nhds hv)
    have h2 : DifferentiableAt ℂ (fun w => (p w, Lsnd w - Lsnd v0)) v := by
      first
        | exact h1.prodMk (Lsnd.differentiableAt.sub_const _)
        | exact h1.prod (Lsnd.differentiableAt.sub_const _)
    exact (A.symm : V d × V (n - d) →L[ℂ] V n).differentiableAt.comp v h2
  have hΨc : ContDiffAt ℂ 1 Ψ v0 := by
    have h1 : ContDiffAt ℂ 1 p v0 := hpC.contDiffAt (hU.mem_nhds hv0)
    have h2 : ContDiffAt ℂ 1 (fun w => (p w, Lsnd w - Lsnd v0)) v0 := by
      first
        | exact h1.prodMk (Lsnd.contDiff.contDiffAt.sub contDiffAt_const)
        | exact h1.prod (Lsnd.contDiff.contDiffAt.sub contDiffAt_const)
    exact (A.symm : V d × V (n - d) →L[ℂ] V n).contDiff.contDiffAt.comp v0 h2
  have hΨd : HasFDerivAt Ψ
      ((ContinuousLinearEquiv.refl ℂ (V n) : V n ≃L[ℂ] V n) : V n →L[ℂ] V n) v0 := by
    have h1 : HasFDerivAt p (fderiv ℂ p v0) v0 :=
      (hp.differentiableAt (hU.mem_nhds hv0)).hasFDerivAt
    have h2 : HasFDerivAt (fun w => (p w, Lsnd w - Lsnd v0))
        ((fderiv ℂ p v0).prod Lsnd) v0 := by
      first
        | exact h1.prodMk (Lsnd.hasFDerivAt.sub_const (Lsnd v0))
        | exact h1.prod (Lsnd.hasFDerivAt.sub_const (Lsnd v0))
    have h3 := (A.symm : V d × V (n - d) →L[ℂ] V n).hasFDerivAt.comp v0 h2
    refine h3.congr_fderiv ?_
    ext1 h
    have hh : ((fderiv ℂ p v0) h, Lsnd h) = A h := Prod.ext (hA h).symm rfl
    simp [hh]
  have hs := hΨc.hasStrictFDerivAt' hΨd (by simp)
  set G : V n → V n := hs.localInverse Ψ (ContinuousLinearEquiv.refl ℂ (V n)) v0 with hGdef
  have hGc : ContDiffAt ℂ 1 G (Ψ v0) := hΨc.to_localInverse hΨd (by simp)
  have hC : ContDiffAt ℝ 1 Ψ v0 := hΨc.restrict_scalars ℝ
  have hcontD : ContinuousAt (fderiv ℝ Ψ) v0 :=
    (hC.fderiv_right (m := 0) (by rw [zero_add])).continuousAt
  have habs : ContinuousAt (fun v => |(fderiv ℝ Ψ v).det|) v0 :=
    continuous_abs.continuousAt.comp
      (ContinuousLinearMap.continuous_det.continuousAt.comp hcontD)
  have hev1 : ∀ᶠ v in 𝓝 v0, G (Ψ v) = v ∧
      |(fderiv ℝ Ψ v).det| < |(fderiv ℝ Ψ v0).det| + 1 :=
    hs.eventually_left_inverse.and (habs.eventually (Iio_mem_nhds (lt_add_one _)))
  set C : ℝ := |(fderiv ℝ Ψ v0).det| + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  obtain ⟨δ1, hδ1, hδ1b⟩ := Metric.eventually_nhds_iff_ball.1 hev1
  obtain ⟨δ2, hδ2, hδ2b⟩ := Metric.isOpen_iff.1 hU v0 hv0
  set δ : ℝ := min δ1 δ2 / 2 with hδdef
  have hδpos : 0 < δ := half_pos (lt_min hδ1 hδ2)
  have hδlt : δ < min δ1 δ2 := half_lt_self (lt_min hδ1 hδ2)
  have hballU : Metric.ball v0 δ ⊆ U := fun v hv =>
    hδ2b (Metric.ball_subset_ball ((hδlt.le).trans (min_le_right _ _)) hv)
  have hballP : ∀ v ∈ Metric.ball v0 δ, G (Ψ v) = v ∧ |(fderiv ℝ Ψ v).det| < C :=
    fun v hv => hδ1b v (Metric.ball_subset_ball ((hδlt.le).trans (min_le_left _ _)) hv)
  refine ⟨δ, hδpos, ?_, ?_⟩
  · exact (Metric.closedBall_subset_ball hδlt).trans
      (fun v hv => hδ2b (Metric.ball_subset_ball (min_le_right _ _) hv))
  have hevB : ∀ᶠ x in 𝓝 (Ψ v0), G x ∈ Metric.ball v0 δ :=
    hs.localInverse_tendsto (Metric.ball_mem_nhds v0 hδpos)
  have hevD : ∀ᶠ x in 𝓝 (Ψ v0), DifferentiableAt ℂ G x :=
    (hGc.eventually (by simp)).mono fun x hx => hx.differentiableAt (by simp)
  have hev2 : ∀ᶠ x in 𝓝 (Ψ v0), Ψ (G x) = x ∧ G x ∈ Metric.ball v0 δ ∧
      DifferentiableAt ℂ G x :=
    Filter.Eventually.and hs.eventually_right_inverse (Filter.Eventually.and hevB hevD)
  rw [hΨ0] at hev2
  obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff_ball.1 hev2
  set As : V d × V (n - d) →L[ℂ] V n := (A.symm : V d × V (n - d) →L[ℂ] V n) with hAs
  set ε : ℝ := r / (‖As‖ + 1) with hεdef
  have hAs1 : 0 < ‖As‖ + 1 := by positivity
  have hε : 0 < ε := div_pos hr hAs1
  set Box : Set (V d × V (n - d)) :=
    Metric.ball (0 : V d) ε ×ˢ Metric.ball (0 : V (n - d)) ε with hBoxdef
  have hBox : ∀ z ∈ Box, A.symm z ∈ Metric.ball (0 : V n) r := by
    intro z hz
    have hz1 : ‖z.1‖ < ε := by simpa using hz.1
    have hz2 : ‖z.2‖ < ε := by simpa using hz.2
    have hzn : ‖z‖ < ε := by rw [Prod.norm_def]; exact max_lt hz1 hz2
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖A.symm z‖ ≤ ‖As‖ * ‖z‖ := As.le_opNorm z
    have h2 : ‖As‖ * ‖z‖ ≤ ‖As‖ * ε := mul_le_mul_of_nonneg_left hzn.le (norm_nonneg _)
    have h3 : ‖As‖ * ε < (‖As‖ + 1) * ε := by nlinarith
    have h4 : (‖As‖ + 1) * ε = r := by rw [hεdef]; field_simp
    linarith
  intro M
  obtain ⟨τ0, hτ0, hblow⟩ := ap_prod_blowup d (n - d) hd (hMVd d) (hMVd (n - d)) hMVI ε hε
    (M * ((K : ℝ) * C))
  refine ⟨τ0, hτ0, fun τ hτ hττ0 u hu => ?_⟩
  have hBm : MeasurableSet Box := measurableSet_ball.prod measurableSet_ball
  have hu' : DifferentiableOn ℂ (fun z => u (G (A.symm z))) Box := by
    intro z hz
    obtain ⟨_, hGb, hGd⟩ := hrb _ (hBox z hz)
    have hu1 : DifferentiableAt ℂ u (G (A.symm z)) :=
      hu.differentiableAt (Metric.isOpen_ball.mem_nhds hGb)
    exact ((hu1.comp _ hGd).comp z As.differentiableAt).differentiableWithinAt
  have hb := hblow τ hτ hττ0 _ hu'
  beta_reduce at hb
  rw [← hBoxdef] at hb
  have hG0 : G 0 = v0 := by
    rw [← hΨ0]
    exact hs.localInverse_apply_image
  have hu0 : u (G (A.symm 0)) = u v0 := by rw [map_zero, hG0]
  set g : V n → ℝ≥0∞ := fun v =>
    ENNReal.ofReal (‖u v‖ ^ 2 * (max (‖p v‖ ^ 2) τ) ^ (-(d : ℝ))) with hgdef
  have hpz : ∀ z ∈ Box, p (G (A.symm z)) = z.1 := by
    intro z hz
    have hR := (hrb _ (hBox z hz)).1
    have := congrArg (fun w => (A w).1) hR
    simpa [Ψ] using this
  have hI1 : ∫⁻ z in Box, ENNReal.ofReal (‖u (G (A.symm z))‖ ^ 2 *
        (max (‖z.1‖ ^ 2) τ) ^ (-(d : ℝ))) = ∫⁻ z in Box, g (G (A.symm z)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem hBm] with z hz
    simp only [g]
    rw [hpz z hz]
  have hI2 : ∫⁻ z in Box, g (G (A.symm z)) =
      (K : ℝ≥0∞) * ∫⁻ x in (A : V n → V d × V (n - d)) ⁻¹' Box, g (G x) :=
    hKeq Box (fun x => g (G x))
  set T : Set (V n) := (A : V n → V d × V (n - d)) ⁻¹' Box with hTdef
  set s : Set (V n) := Metric.ball v0 δ ∩ Ψ ⁻¹' T with hsdef
  have hTopen : IsOpen T := (Metric.isOpen_ball.prod Metric.isOpen_ball).preimage A.continuous
  have hΨcont : ContinuousOn Ψ (Metric.ball v0 δ) := fun v hv =>
    (hΨdiff v (hballU hv)).continuousAt.continuousWithinAt
  have hsm : MeasurableSet s :=
    (hΨcont.isOpen_inter_preimage Metric.isOpen_ball hTopen).measurableSet
  have himg : Ψ '' s = T := by
    ext x
    constructor
    · rintro ⟨v, ⟨_, hv⟩, rfl⟩
      exact hv
    · intro hx
      have hxr : x ∈ Metric.ball (0 : V n) r := by
        have := hBox (A x) hx
        simpa using this
      obtain ⟨hR, hB, _⟩ := hrb x hxr
      refine ⟨G x, ⟨hB, ?_⟩, hR⟩
      rw [Set.mem_preimage, hR]
      exact hx
  have hinj : Set.InjOn Ψ s := by
    intro v hv w hw hvw
    rw [← (hballP v hv.1).1, ← (hballP w hw.1).1, hvw]
  have hderiv : ∀ v ∈ s, HasFDerivWithinAt Ψ (fderiv ℝ Ψ v) s v := fun v hv =>
    ((hΨdiff v (hballU hv.1)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsm hderiv hinj
    (fun x => g (G x))
  rw [himg] at hcv
  have hbd : ∫⁻ v in s, ENNReal.ofReal |(fderiv ℝ Ψ v).det| * g (G (Ψ v))
      ≤ ENNReal.ofReal C * ∫⁻ v in Metric.ball v0 δ, g v := by
    calc ∫⁻ v in s, ENNReal.ofReal |(fderiv ℝ Ψ v).det| * g (G (Ψ v))
        ≤ ∫⁻ v in s, ENNReal.ofReal C * g v := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hsm] with v hv
          obtain ⟨hL, hD⟩ := hballP v hv.1
          rw [hL]
          exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hD.le) (by simp)
      _ = ENNReal.ofReal C * ∫⁻ v in s, g v := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ∫⁻ v in Metric.ball v0 δ, g v :=
          mul_le_mul_of_nonneg_left (lintegral_mono_set Set.inter_subset_left) (by simp)
  have hmain : ENNReal.ofReal (M * ((K : ℝ) * C) * ‖u v0‖ ^ 2)
      ≤ (K : ℝ≥0∞) * (ENNReal.ofReal C * ∫⁻ v in Metric.ball v0 δ, g v) := by
    have h := hb
    rw [hu0, hI1, hI2, hcv] at h
    exact h.trans (mul_le_mul_of_nonneg_left hbd (by simp))
  have hKC : (0 : ℝ) ≤ (K : ℝ) * C := mul_nonneg K.coe_nonneg hCpos.le
  rw [show M * ((K : ℝ) * C) * ‖u v0‖ ^ 2 = ((K : ℝ) * C) * (M * ‖u v0‖ ^ 2) by ring,
    ENNReal.ofReal_mul hKC, ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
    ← mul_assoc] at hmain
  have h0 : (K : ℝ≥0∞) * ENNReal.ofReal C ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hK.ne') (by simpa using hCpos)
  have htop : (K : ℝ≥0∞) * ENNReal.ofReal C ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  first
    | exact ENNReal.le_of_mul_le_mul_left hmain h0 htop
    | exact (ENNReal.mul_le_mul_iff_right h0 htop).1 hmain
    | exact (ENNReal.mul_le_mul_iff_left h0 htop).1 hmain
    | exact (ENNReal.mul_le_mul_left h0 htop).1 hmain
end ReciprocityTheory.L2DbarEstimates.Y
