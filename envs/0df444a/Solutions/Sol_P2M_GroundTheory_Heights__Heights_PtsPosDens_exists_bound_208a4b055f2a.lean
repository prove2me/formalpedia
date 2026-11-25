-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsPosDens_exists_bound_208a4b055f2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:47:45.155891+00:00
-- url     : https://prove2.me/submissions/b144f042-6e59-4f88-894b-a955cdf266cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsPosDensIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsSumMeasurableA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsPosDensMeasurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian
open GroundTheory.Heights₂.Heights.PtsPosDens
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PtsPosDens
theorem _root_.solution {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) :
    ∃ M : ℝ, ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → |g z| ≤ M := by
  set T : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ‖fun i : ι k => z ⟨k, i⟩‖ = 1} with hTdef
  have hTc : IsClosed T := by
    rw [hTdef, Set.ofPred_forall]
    exact isClosed_iInter fun k =>
      isClosed_eq (continuous_norm.comp (continuous_pi fun i => continuous_apply _)) continuous_const
  have hTb : T ⊆ Metric.closedBall 0 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    have h1 := norm_le_pi_norm (fun i : ι p.1 => z ⟨p.1, i⟩) p.2
    rw [hz p.1] at h1
    exact h1
  have hTK : IsCompact T := Metric.isCompact_of_isClosed_isBounded hTc (Metric.isBounded_closedBall.subset hTb)
  have hTU : T ⊆ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra h
    push Not at h
    have h0 : (fun i : ι k => z ⟨k, i⟩) = 0 := funext h
    have := hz k
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  obtain ⟨M, hM⟩ := hTK.exists_bound_of_continuousOn (hg.1.continuousOn.mono hTU)
  refine ⟨M, fun z hz => ?_⟩
  have hb : ∀ k, (fun i : ι k => z ⟨k, i⟩) ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hz k
    exact hi (congrFun h0 i)
  set c : K → ℂ := fun k => ((‖fun i : ι k => z ⟨k, i⟩‖ : ℝ) : ℂ)⁻¹ with hcdef
  have hc : ∀ k, c k ≠ 0 := fun k =>
    inv_ne_zero (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hb k)))
  have hmem : (fun p : Σ k, ι k => c p.1 * z p) ∈ T := by
    intro k
    have : (fun i : ι k => c k * z ⟨k, i⟩) = c k • fun i : ι k => z ⟨k, i⟩ := rfl
    rw [this, norm_smul, hcdef]
    simp only [norm_inv, Complex.norm_real, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 (hb k))
  rw [← hg.2 c z hc]
  exact hM _ hmem
end GroundTheory.Heights₂.Heights.PtsPosDens
