-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_disc_props_e21f27b8168e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:27:27.216413+00:00
-- url     : https://prove2.me/submissions/db6b33f2-a8a8-4d15-9bd2-5fb2b5671e10

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedBranchSameOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPuncturedCurveDiscInverse
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPuncturedBranchSameOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PuncturedBranchSameOrder_const_mem_ball_iff_5c748a61eaf1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder
namespace GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder
theorem _root_.solution {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (b : VarBranch I 1 q) :
    DifferentiableOn ℂ (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) ∧
    Set.InjOn (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) ∧
    Set.MapsTo (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) (zeroSet I) ∧
    (b.toFun fun _ ↦ (0 : ℂ)) = q ∧
    ∀ x, x ∈ b.image ↔ ∃ σ ∈ Metric.ball (0 : ℂ) b.radius, (b.toFun fun _ ↦ σ) = x := by
  have hι : Differentiable ℂ (fun τ : ℂ ↦ fun _ : Fin 1 ↦ τ) := differentiable_pi.2 fun _ ↦ differentiable_id
  refine ⟨b.differentiableOn.comp hι.differentiableOn fun τ hτ ↦ (const_mem_ball_iff τ _).2 hτ,
    fun s hs t ht h ↦ congrFun (b.injOn ((const_mem_ball_iff s _).2 hs) ((const_mem_ball_iff t _).2 ht) h) 0,
    fun τ hτ ↦ b.mapsTo ((const_mem_ball_iff τ _).2 hτ), b.map_zero, fun x ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht, rfl⟩
    have ht' : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
    refine ⟨t 0, (const_mem_ball_iff _ _).1 ?_, by rw [ht']⟩
    rw [ht']
    exact ht
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, (const_mem_ball_iff σ _).2 hσ, rfl⟩
end GroundTheory.Heights₂.Heights.PuncturedBranchSameOrder
