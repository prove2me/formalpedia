-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_BranchProperAtPoint_proof_e08da62d748d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:57:49.402369+00:00
-- url     : https://prove2.me/submissions/9ca0d8ee-fdc9-42e1-bbe5-8261b84174c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchProperAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchAwayFromRim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchProperAtPoint

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
namespace BranchProperAtPoint
theorem _root_.solution (hrim : BranchAwayFromRim.Statement) :
    BranchProperAtPoint.Statement := by
  intro n k J u p x m γ hJ hdim hu hcov hdisj b s hs hsx P hP
  obtain ⟨ε₀, hε₀, ρ, hρ, hrimb⟩ := hrim n k J u p x m γ hJ hdim hu hcov hdisj b
  obtain ⟨P', hP'P, hP'o, hsP'⟩ := mem_nhds_iff.mp hP
  set K : Set (Fin k → ℂ) := Metric.closedBall 0 ρ \ P' with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 ρ).diff hP'o
  have hKD : K ⊆ Metric.ball 0 (γ b).radius := fun τ hτ =>
    mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hτ.1) hρ)
  have hcont : ContinuousOn (γ b).toFun K := (γ b).differentiableOn.continuousOn.mono hKD
  have hxK : x ∉ (γ b).toFun '' K := by
    rintro ⟨τ, hτK, hτx⟩
    have hτs : τ = s := (γ b).injOn (hKD hτK) hs (hτx.trans hsx.symm)
    exact hτK.2 (hτs ▸ hsP')
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.isOpen_iff.mp (hKc.image_of_continuousOn hcont).isClosed.isOpen_compl x hxK
  refine ⟨min ε₀ δ, lt_min hε₀ hδ, fun τ hτ hfτ => ?_⟩
  have h1 : ‖τ‖ ≤ ρ := hrimb τ hτ (Metric.ball_subset_ball (min_le_left _ _) hfτ)
  by_contra hτP
  have hτK : τ ∈ K := ⟨mem_closedBall_zero_iff.mpr h1, fun h => hτP (hP'P h)⟩
  exact hball (Metric.ball_subset_ball (min_le_right _ _) hfτ) ⟨τ, hτK, rfl⟩
end BranchProperAtPoint
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
