-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IrreducibleFiniteGermProjectionOpenAt_proof_f2d02b110817
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:06.546641+00:00
-- url     : https://prove2.me/submissions/d141274b-11fb-4004-8cad-0fc0222a1cfe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleFiniteGermProjectionOpenAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIrreducibleGermPointsOffDiscriminant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIrreducibleFiniteGermProjectionOpenAt

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
open Topology Metric Filter Set
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace IrreducibleFiniteGermProjectionOpenAt
theorem _root_.solution
    (hpts : IrreducibleGermPointsOffDiscriminant.Statement) :
    IrreducibleFiniteGermProjectionOpenAt.Statement := by
  intro σ _ X x d A hX hirr hiso hinj V hV
  obtain ⟨δ, hδa, hδne, hδpts⟩ := hpts σ X x d A hX hirr hiso hinj
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hNo.mem_nhds hxN))
  set r' := r / 2 with hr'
  have hr'0 : 0 < r' := by positivity
  have hcb : closedBall x r' ⊆ V ∩ N := (closedBall_subset_ball (by linarith)).trans hrV

  set K : Set (σ → ℂ) := closedBall x r' ∩ ⋂ i, (closedBall x r' ∩ f i ⁻¹' {0}) with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x r').of_isClosed_subset ?_ inter_subset_left
    refine isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono (hcb.trans inter_subset_right)).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_singleton
  have hKV : A '' K ⊆ A '' (X ∩ V) := by
    refine image_mono fun z hz => ?_
    have hzN : z ∈ N := (hcb hz.1).2
    have hzX : z ∈ X ∩ N := by
      rw [hXN]
      exact ⟨hzN, fun i => by simpa using ((mem_iInter.mp hz.2) i).2⟩
    exact ⟨hzX.1, (hcb hz.1).1⟩
  have hball : ∀ z ∈ X ∩ ball x r', z ∈ K := by
    intro z hz
    have hzcb : z ∈ closedBall x r' := ball_subset_closedBall hz.2
    have hzN : z ∈ X ∩ N := ⟨hz.1, (hcb hzcb).2⟩
    rw [hXN] at hzN
    exact ⟨hzcb, mem_iInter.mpr fun i => ⟨hzcb, by simpa using hzN.2 i⟩⟩

  obtain ⟨ε₁, hε₁, hε₁a⟩ := hδa.exists_ball_analyticOnNhd
  obtain ⟨ε₂, hε₂, hε₂p⟩ := Metric.eventually_nhds_iff.mp (hδpts (ball x r') (ball_mem_nhds x hr'0))
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hDa : AnalyticOnNhd ℂ δ (ball (A x) ε) := hε₁a.mono (ball_subset_ball (min_le_left _ _))
  have hsub : {y | y ∈ ball (A x) ε ∧ δ y ≠ 0} ⊆ A '' K := by
    rintro y ⟨hy, hδy⟩
    have hy2 : dist y (A x) < ε₂ := lt_of_lt_of_le (mem_ball.mp hy) (min_le_right _ _)
    obtain ⟨x', hx', rfl⟩ := hε₂p hy2 hδy
    exact ⟨x', hball x' hx', rfl⟩
  have hD : ball (A x) ε ⊆ A '' K := by
    intro y hy
    refine (hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsub (mem_closure_iff_frequently.mpr ?_)
    intro hev
    have hev' : δ =ᶠ[𝓝 y] 0 := by
      filter_upwards [hev, isOpen_ball.mem_nhds hy] with z hz hzD
      by_contra hz0
      exact hz ⟨hzD, hz0⟩
    have hzero := hDa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (A x) ε).isPreconnected hy hev'
    apply hδne
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz using hzero hz
  exact Filter.mem_of_superset (ball_mem_nhds (A x) hε) (hD.trans hKV)
end IrreducibleFiniteGermProjectionOpenAt
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
