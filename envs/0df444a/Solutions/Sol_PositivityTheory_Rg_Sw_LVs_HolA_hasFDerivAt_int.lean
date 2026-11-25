-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.HolA.hasFDerivAt_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:47:45.216376+00:00
-- url     : https://prove2.me/submissions/0bb2e043-dbc1-4c8e-9bc2-70254f6414af

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_HasFDerivAtInt
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_HolA_integrable_of_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.HolA
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {Kg : Type*} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg] [BorelSpace Kg]
  {μ : Measure Kg} [IsFiniteMeasure μ]
namespace PositivityTheory.Rg.Sw.LVs.HolA
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
    {Ω : Set E} (hΩ : IsOpen Ω) {Φ : Kg → E → W} {Φ' : Kg → E → (E →L[ℂ] W)}
    (hc : ContinuousOn (fun y : Kg × E => Φ y.1 y.2) (univ ×ˢ Ω))
    (hc' : ContinuousOn (fun y : Kg × E => Φ' y.1 y.2) (univ ×ˢ Ω))
    (hd : ∀ k, ∀ x ∈ Ω, HasFDerivAt (Φ k) (Φ' k x) x) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    HasFDerivAt (fun x => ∫ k, Φ k x ∂μ) (∫ k, Φ' k x₀ ∂μ) x₀ := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  have hsub : closedBall x₀ (r / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hrΩ
  have hK : IsCompact ((univ : Set Kg) ×ˢ closedBall x₀ (r / 2)) := isCompact_univ.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc'.mono (prod_mono subset_rfl hsub))
  have cont_k : ∀ x ∈ Ω, Continuous fun k => Φ k x := fun x hx =>
    continuousOn_univ.mp (hc.comp (f := fun k : Kg => (k, x)) (Continuous.continuousOn (by fun_prop))
      fun k _ => ⟨mem_univ _, hx⟩)
  have cont_k' : ∀ x ∈ Ω, Continuous fun k => Φ' k x := fun x hx =>
    continuousOn_univ.mp (hc'.comp (f := fun k : Kg => (k, x)) (Continuous.continuousOn (by fun_prop))
      fun k _ => ⟨mem_univ _, hx⟩)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (F := fun x k => Φ k x)
    (F' := fun x k => Φ' k x) (bound := fun _ => C) (ball_mem_nhds x₀ (half_pos hr)) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hΩ.mem_nhds hx₀] with x hx
    exact (integrable_of_cont (cont_k x hx)).aestronglyMeasurable
  · exact integrable_of_cont (cont_k x₀ hx₀)
  · exact (integrable_of_cont (cont_k' x₀ hx₀)).aestronglyMeasurable
  · exact Eventually.of_forall fun k x hx => hC (k, x) ⟨mem_univ _, ball_subset_closedBall hx⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun k x hx => hd k x (hsub (ball_subset_closedBall hx))
end PositivityTheory.Rg.Sw.LVs.HolA
