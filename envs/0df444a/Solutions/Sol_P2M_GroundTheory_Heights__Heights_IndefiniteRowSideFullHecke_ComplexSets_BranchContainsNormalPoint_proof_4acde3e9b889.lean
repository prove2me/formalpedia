-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_BranchContainsNormalPoint_proof_4acde3e9b889
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:31.166507+00:00
-- url     : https://prove2.me/submissions/b1040a6d-f991-4bbb-b613-6161906e2d8d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchContainsNormalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicOnSubset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInverseHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalRiemannExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalMaximumPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchContainsNormalPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicOnSubset_continuousWithinAt_7f073503ccef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace BranchContainsNormalPoint
theorem _root_.solution (hirr : NormalLocallyIrreducible.Statement)
    (hinv : BranchInverseHolomorphic.Statement) (hext : NormalRiemannExtension.Statement)
    (hmax : NormalMaximumPrinciple.Statement) : BranchContainsNormalPoint.Statement := by
  intro σ _ I h w k r φ B hI hIc hh hw hφd hφi hφZ hB hfill
  obtain ⟨B', hB'o, hwB', hB'B, -, hdense⟩ := hirr σ I h w hI hIc hh hw B hB
  set P := (zeroSetIn I ∩ B') \ {z | eval z h = 0} with hP
  have hPfill : P ⊆ φ '' Metric.ball 0 r := fun z hz => hfill ⟨⟨hz.1.1, hB'B hz.1.2⟩, hz.2⟩
  have hPsub : P ⊆ zeroSetIn I ∩ B' := fun y hy => hy.1
  have hwcl : w ∈ closure P := hdense ⟨hw, hwB'⟩
  obtain ⟨ψ, hψ, hψφ⟩ := hinv σ I h w k r φ B hI hIc hh hw hφd hφi hφZ hB hfill
  have hPψ : ∀ z ∈ P, ψ z ∈ Metric.ball (0 : Fin k → ℂ) r ∧ φ (ψ z) = z := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hPfill hz
    rw [hψφ t ht]
    exact ⟨ht, rfl⟩
  have hPlt : ∀ z ∈ P, ∀ j, ‖ψ z j‖ < r := fun z hz j =>
    (norm_le_pi_norm (ψ z) j).trans_lt (mem_ball_zero_iff.mp (hPψ z hz).1)

  have hcoord : ∀ j : Fin k, ∃ g : (σ → ℂ) → ℂ, HolomorphicOnSubset g (zeroSetIn I ∩ B') ∧
      Set.EqOn g (fun z => ψ z j) P := by
    intro j
    refine hext σ I h B' (fun z => ψ z j) hI hIc hh hB'o ?_ ?_
    · intro z hz
      obtain ⟨U, hUo, hzU, F, hF, hFeq⟩ := hψ z (hPfill hz)
      exact ⟨U, hUo, hzU, fun y => F y j, differentiableOn_pi.mp hF j,
        fun y hy => congrFun (hFeq ⟨hPfill hy.1, hy.2⟩) j⟩
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r)).subset ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hPlt z hz j).le
  choose g hg hgeq using hcoord

  have hgle : ∀ j, ∀ z ∈ zeroSetIn I ∩ B', ‖g j z‖ ≤ r := by
    intro j z hz
    have hcl := (((hg j).continuousWithinAt hz).mono hPsub).mem_closure_image (hdense hz)
    have hsub : g j '' P ⊆ Metric.closedBall 0 r := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right, hgeq j hy]
      exact (hPlt y hy j).le
    have := closure_minimal hsub Metric.isClosed_closedBall hcl
    rwa [Metric.mem_closedBall, dist_zero_right] at this

  have hglt : ∀ j, ‖g j w‖ < r := by
    intro j
    by_contra hlt
    have heq : ‖g j w‖ = r := le_antisymm (hgle j w ⟨hw, hwB'⟩) (not_lt.mp hlt)
    have hev := hmax σ I w B' (g j) hI hIc hw (hB'o.mem_nhds hwB') (hg j)
      (fun z hz => (hgle j z hz).trans heq.ge)
    obtain ⟨z, hz, hzP⟩ := mem_closure_iff_nhds.mp hwcl _ hev
    have h1 : ‖g j z‖ < r := (congrArg norm (hgeq j hzP)).trans_lt (hPlt z hzP j)
    rw [hz hzP.1.1, heq] at h1
    exact lt_irrefl r h1
  have hr : 0 < r := by
    obtain ⟨z, -, hzP⟩ := mem_closure_iff_nhds.mp hwcl _ Filter.univ_mem
    exact (norm_nonneg _).trans_lt (mem_ball_zero_iff.mp (hPψ z hzP).1)
  set t₀ : Fin k → ℂ := fun j => g j w with ht₀
  have ht₀Δ : t₀ ∈ Metric.ball (0 : Fin k → ℂ) r := mem_ball_zero_iff.mpr ((pi_norm_lt_iff hr).mpr hglt)
  refine ⟨t₀, ht₀Δ, ?_⟩

  have : (𝓝[P] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hwcl
  have hG : Tendsto (fun z => fun j => g j z) (𝓝[P] w) (𝓝 t₀) :=
    tendsto_pi_nhds.mpr fun j => (((hg j).continuousWithinAt ⟨hw, hwB'⟩).mono hPsub).tendsto
  have hφc : ContinuousAt φ t₀ := (hφd.differentiableAt (Metric.isOpen_ball.mem_nhds ht₀Δ)).continuousAt
  have h1 : Tendsto (fun z => φ (fun j => g j z)) (𝓝[P] w) (𝓝 (φ t₀)) := hφc.tendsto.comp hG
  have h2 : Tendsto (fun z => φ (fun j => g j z)) (𝓝[P] w) (𝓝 w) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hgz : (fun j => g j z) = ψ z := funext fun j => hgeq j hz
    rw [hgz, (hPψ z hz).2]
    rfl
  exact tendsto_nhds_unique h1 h2
end BranchContainsNormalPoint
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
