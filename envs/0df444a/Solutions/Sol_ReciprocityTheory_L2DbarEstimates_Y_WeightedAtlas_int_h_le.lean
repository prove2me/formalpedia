-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.int_h_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:31:46.783858+00:00
-- url     : https://prove2.me/submissions/fada3c9b-df83-47ff-9210-2e064014c35c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxK
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxL
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_continuous_sqn_of_isSec
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution {Sf : Finset Y} (D : CutData A Sf) {L : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) {ps1 : Y → ℝ}
    (hps1 : A.SmoothFn ps1) (η : ℝ) (hTS : ∀ P ∈ Sf, ∀ y ∈ D.T P, 0 < A.sqn L s y) (Ch : ℝ) :
    ∃ Hb : ℝ≥0∞, Hb < ⊤ ∧ ∀ δ : ℝ, 0 < δ →
      ∫⁻ y, (⋃ P ∈ Sf, D.T P).indicator (fun _ => ENNReal.ofReal Ch) y *
        ENNReal.ofReal (Real.exp (-A.psD L w s ps1 η δ y)) ∂A.mu ≤ Hb := by
  classical
  have hTeq : ∀ P, D.T P = (A.chart (A.pick P)).symm ''
      (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P)) :=
    fun P => rfl
  have hS : ∀ P, IsCompact
      (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P)) :=
    fun P => (isCompact_closedBall _ _).diff isOpen_ball
  have hStgt : ∀ P ∈ Sf, ∀ v ∈ closedBall (A.chart (A.pick P) P) (D.r2 P) \
      ball (A.chart (A.pick P) P) (D.r1 P), v ∈ (A.chart (A.pick P)).target :=
    fun P hP v hv => (D.8 P hP hv.1).1
  have hTc : ∀ P ∈ Sf, IsCompact (D.T P) := by
    intro P hP
    rw [hTeq P]
    exact (hS P).image_of_continuousOn
      ((A.chart (A.pick P)).continuousOn_symm.mono fun v hv => hStgt P hP v hv)
  have hμT : ∀ P ∈ Sf, A.mu (D.T P) < ⊤ := by
    intro P hP
    have hTs : D.T P ⊆ (A.chart (A.pick P)).source := by
      rw [hTeq P]
      rintro _ ⟨v, hv, rfl⟩
      exact (A.chart (A.pick P)).map_target (hStgt P hP v hv)
    rw [A.mu_chart (A.pick P) (D.T P) (hTc P hP).isClosed.measurableSet hTs]
    have himg : (A.chart (A.pick P)) '' D.T P =
        closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P) := by
      rw [hTeq P, Set.image_image]
      exact (Set.image_congr fun v hv => (A.chart (A.pick P)).right_inv (hStgt P hP v hv)).trans
        (Set.image_id' _)
    rw [himg]
    have hcont : ContinuousOn
        (fun v => Real.exp (A.ph A.kap (A.pick P) ((A.chart (A.pick P)).symm v)))
        (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P)) :=
      Real.continuous_exp.comp_continuousOn
        ((A.smooth_ph A.kap (A.pick P)).continuousOn.mono fun v hv => hStgt P hP v hv)
    obtain ⟨C', hC'⟩ := (hS P).exists_bound_of_continuousOn hcont
    calc ∫⁻ v in closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P),
          ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick P) ((A.chart (A.pick P)).symm v)))
        ≤ ∫⁻ v in closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P),
          ENNReal.ofReal C' :=
          setLIntegral_mono' (hS P).isClosed.measurableSet fun v hv =>
            ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC' v hv))
      _ = ENNReal.ofReal C' * volume
          (closedBall (A.chart (A.pick P) P) (D.r2 P) \ ball (A.chart (A.pick P) P) (D.r1 P)) :=
          setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hS P).measure_lt_top
  obtain ⟨K, hK⟩ : ∃ K, K = ⋃ P ∈ Sf, D.T P := ⟨_, rfl⟩
  rw [← hK]
  have hKc : IsCompact K := by
    rw [hK]
    exact Sf.isCompact_biUnion hTc
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hμK : A.mu K < ⊤ := by
    rw [hK]
    exact (measure_biUnion_finset_le Sf _).trans_lt (ENNReal.sum_lt_top.mpr fun P hP => hμT P hP)
  have hsK : ∀ y ∈ K, 0 < A.sqn L s y := by
    intro y hy
    rw [hK, Set.mem_iUnion₂] at hy
    obtain ⟨P, hP, hyP⟩ := hy
    exact hTS P hP y hyP
  have hps1c : Continuous ps1 := by
    rw [continuous_iff_continuousAt]
    intro y0
    have hy0 := A.mem_pick y0
    have h1 := (hps1 (A.pick y0)).continuousOn.comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    have h2 : ContinuousOn ps1 (A.chart (A.pick y0)).source :=
      h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
    exact h2.continuousAt ((A.chart (A.pick y0)).open_source.mem_nhds hy0)
  have hwc : Continuous (A.sqn L w) := A.continuous_sqn_of_isSec hD.sec_w
  have hsc : Continuous (A.sqn L s) := A.continuous_sqn_of_isSec hD.sec_s
  have hwpos : ∀ y, 0 < A.sqn L w y := by
    intro y
    obtain ⟨k, hk⟩ := hD.no_common_zero y
    have hle : A.nsq L (w k) y ≤ A.sqn L w y :=
      Finset.single_le_sum (f := fun k => A.nsq L (w k) y)
        (fun j _ => by simp only [nsq]; positivity) (Finset.mem_univ k)
    have hpos : 0 < A.nsq L (w k) y := by
      simp only [nsq]
      exact mul_pos (pow_pos (norm_pos_iff.mpr hk) 2) (Real.exp_pos _)
    linarith
  have hGc : ContinuousOn (fun y => Real.exp (-ps1 y - η * Real.log (A.sqn L w y) -
      (n : ℝ) * Real.log (A.sqn L s y))) K := by
    apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.sub
    · exact (hps1c.neg.sub (continuous_const.mul (hwc.log fun y => (hwpos y).ne'))).continuousOn
    · exact continuousOn_const.mul (hsc.continuousOn.log fun y hy => (hsK y hy).ne')
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hGc
  have hbound : ∀ y ∈ K, ∀ δ : ℝ, 0 < δ → Real.exp (-A.psD L w s ps1 η δ y) ≤ C := by
    intro y hy δ hδ
    refine le_trans ?_ ((Real.le_norm_self _).trans (hC y hy))
    apply Real.exp_le_exp.mpr
    unfold psD
    have h1 : Real.log (A.sqn L s y) ≤ Real.log (A.sqn L s y + δ) :=
      Real.log_le_log (hsK y hy) (by linarith)
    have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  refine ⟨ENNReal.ofReal Ch * ENNReal.ofReal C * A.mu K,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hμK,
    fun δ hδ => ?_⟩
  calc ∫⁻ y, K.indicator (fun _ => ENNReal.ofReal Ch) y *
        ENNReal.ofReal (Real.exp (-A.psD L w s ps1 η δ y)) ∂A.mu
      ≤ ∫⁻ y, K.indicator (fun _ => ENNReal.ofReal Ch * ENNReal.ofReal C) y ∂A.mu := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ K
        · simp only [Set.indicator_of_mem hy]
          exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hbound y hy δ hδ))
        · simp [hy]
    _ = ENNReal.ofReal Ch * ENNReal.ofReal C * A.mu K := lintegral_indicator_const hKm _
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
