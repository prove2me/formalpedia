-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.exists_chart_bump
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:24:56.918897+00:00
-- url     : https://prove2.me/submissions/1e3c82bb-f2c2-48cd-ba24-e3e0a9d0fba6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (U : Set M) (hU : IsOpen U) (x : M) (hx : x ∈ U) :
    ∃ (e : OpenPartialHomeomorph M (V n)) (ψ : M → ℝ),
      IsChart n z e ∧ SmoothR n z ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ e.source ∩ U ∧
      (∀ y, 0 ≤ ψ y ∧ ψ y ≤ 1) ∧ ∀ᶠ y in 𝓝 x, ψ y = 1 := by
  have hz' : ∀ y, ∃ e : OpenPartialHomeomorph M (V n), y ∈ e.source ∧ z = e := hz
  obtain ⟨e, hxe, hze⟩ := hz' x
  have he : IsChart n z e := fun y _ => congrFun hze y
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hxO : e x ∈ e.target ∩ e.symm ⁻¹' U := ⟨e.map_source hxe, by simp [e.left_inv hxe, hx]⟩
  obtain ⟨r, hr, hrO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds hxO)
  let φ : ContDiffBump (e x) := ⟨r / 2, r, by positivity, by linarith⟩
  let ψ : M → ℝ := e.source.indicator (fun y => φ (e y))
  set K := e.symm '' Metric.closedBall (e x) r with hKdef
  have hKt : Metric.closedBall (e x) r ⊆ e.target := fun w hw => (hrO hw).1
  have hKc : IsCompact K :=
    (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono hKt)
  have hKs : K ⊆ e.source ∩ U := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨e.map_target (hrO hw).1, (hrO hw).2⟩
  have hsupp : Function.support ψ ⊆ K := by
    intro y hy
    rw [Function.mem_support] at hy
    by_cases hys : y ∈ e.source
    · have h1 : φ (e y) ≠ 0 := by simpa [ψ, Set.indicator_of_mem hys] using hy
      have h2 : e y ∈ Metric.ball (e x) r := by
        rw [← φ.support_eq]; exact h1
      exact ⟨e y, Metric.ball_subset_closedBall h2, e.left_inv hys⟩
    · exact absurd (by simp [ψ, Set.indicator_apply, hys]) hy
  have htsK : tsupport ψ ⊆ K := closure_minimal hsupp hKc.isClosed
  refine ⟨e, ψ, he, ?_, hKc.of_isClosed_subset (isClosed_tsupport _) htsK, htsK.trans hKs,
    fun y => ?_, ?_⟩
  · intro e' he' w hw
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hys : e'.symm w ∈ e.source
    · have hc := e'.continuousAt_symm hw
      have h1 : (fun y => (ψ y : ℂ)) ∘ e'.symm =ᶠ[𝓝 w] fun w' => ((φ w' : ℝ) : ℂ) := by
        filter_upwards [e'.open_target.mem_nhds hw, hc (e.open_source.mem_nhds hys)] with w' hw' hw2
        have h2 : e (e'.symm w') = w' := by
          rw [← congrFun hze, he' (e'.map_target hw'), e'.right_inv hw']
        have hw3 : e'.symm w' ∈ e.source := hw2
        simp only [Function.comp_apply, ψ, Set.indicator_of_mem hw3, h2]
      have h3 : ContDiff ℝ ∞ (fun w' => ((φ w' : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp φ.contDiff
      exact h3.contDiffAt.congr_of_eventuallyEq h1
    · have hc := e'.continuousAt_symm hw
      have hyK : e'.symm w ∉ K := fun h => hys (hKs h).1
      have h1 : (fun y => (ψ y : ℂ)) ∘ e'.symm =ᶠ[𝓝 w] fun _ => (0 : ℂ) := by
        filter_upwards [hc (hKc.isClosed.isOpen_compl.mem_nhds hyK)] with w' hw'
        have h2 : ψ (e'.symm w') = 0 := Function.notMem_support.mp (fun h => hw' (hsupp h))
        simp [h2]
      exact contDiffAt_const.congr_of_eventuallyEq h1
  · by_cases hys : y ∈ e.source
    · simp only [ψ, Set.indicator_of_mem hys]
      exact ⟨φ.nonneg, φ.le_one⟩
    · simp [ψ, Set.indicator_apply, hys]
  · have h1 : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e x) (r / 2)) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    filter_upwards [h1.mem_nhds ⟨hxe, Metric.mem_ball_self (by positivity)⟩] with y hy
    simp only [ψ, Set.indicator_of_mem hy.1]
    exact φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy.2)
end ReciprocityTheory.L2DbarEstimates
