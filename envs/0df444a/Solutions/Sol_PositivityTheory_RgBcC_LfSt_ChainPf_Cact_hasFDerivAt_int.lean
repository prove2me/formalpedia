-- Prove2me | solution 1 for PositivityTheory.RgBcC.LfSt.ChainPf.Cact.hasFDerivAt_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:15.730934+00:00
-- url     : https://prove2.me/submissions/e1dffd63-3ed7-4513-87eb-d7bb6a7d66eb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ArchimedeanGelfandKernels_LeftEquivariantFunctions_GLMatrixDerivatives_ChainOfCactA
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_contDiffOn_pd
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_hasFDerivAt_pd
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_pd_eq_zero
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_continuous_slice
import Theorems.Thm_PositivityTheory_RgBcC_LfSt_ChainPf_Cact_integrable_slice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Set
open scoped ContDiff
open PositivityTheory PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Cact
variable {H Z : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {Γ : Type} [TopologicalSpace Γ] [T2Space Γ] [MeasurableSpace Γ] [BorelSpace Γ]
variable {O : Set H} {OZ : Set Z}
variable (μ : Measure Γ) [IsFiniteMeasureOnCompacts μ] {ι : Γ → Z}
namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact
theorem _root_.solution {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {Φ : H × Z → W} (hO : IsOpen O) (hOZ : IsOpen OZ) (hιc : Continuous ι) (hι : ∀ y, ι y ∈ OZ)
    (hΦ : ContDiffOn ℝ ∞ Φ (O ×ˢ OZ)) (hS : LocSupp O ι Φ) {x₀ : H} (hx₀ : x₀ ∈ O) :
    HasFDerivAt (fun x => ∫ y : Γ, Φ (x, ι y) ∂μ) (∫ y : Γ, pd Φ (x₀, ι y) ∂μ) x₀ := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℝ W
  haveI : ProperSpace H := FiniteDimensional.proper ℝ H
  obtain ⟨U, hUo, hxU, hUO, K, hK, hKz⟩ := hS x₀ hx₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUo x₀ hxU
  have hcb : closedBall x₀ (r / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hrU
  have hpdc : ContinuousOn (pd Φ) (O ×ˢ OZ) := (contDiffOn_pd hO hOZ hΦ).continuousOn
  have hcomp : IsCompact (closedBall x₀ (r / 2) ×ˢ K) := (isCompact_closedBall x₀ (r / 2)).prod hK
  have hcont : ContinuousOn (fun q : H × Γ => ‖pd Φ (q.1, ι q.2)‖) (closedBall x₀ (r / 2) ×ˢ K) := by
    refine (hpdc.comp (continuous_fst.prodMk (hιc.comp continuous_snd)).continuousOn ?_).norm
    intro q hq
    exact ⟨hUO (hcb hq.1), hι q.2⟩
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (F' := fun x y => pd Φ (x, ι y)) (s := ball x₀ (r / 2))
    (bound := K.indicator fun _ => C) (ball_mem_nhds x₀ (by linarith)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hUo.mem_nhds hxU] with x hx
    exact (continuous_slice hιc hι hΦ.continuousOn (hUO hx)).aestronglyMeasurable
  · exact integrable_slice μ hιc hι hΦ.continuousOn hx₀ hK fun y hy => hKz x₀ hxU y hy
  · exact (continuous_slice hιc hι hpdc hx₀).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y x hx => ?_
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
      have := hC (x, y) ⟨ball_subset_closedBall hx, hy⟩
      simpa using this
    · rw [indicator_of_notMem hy, pd_eq_zero hO hOZ hΦ hUo hUO (hι y) (fun x' hx' => hKz x' hx' y hy)
        (hcb (ball_subset_closedBall hx))]
      simp
  · exact (integrable_indicator_iff hKm).2 (integrableOn_const hK.measure_lt_top.ne)
  · exact Filter.Eventually.of_forall fun y x hx =>
      hasFDerivAt_pd hO hOZ hΦ (hUO (hcb (ball_subset_closedBall hx))) (hι y)
end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
