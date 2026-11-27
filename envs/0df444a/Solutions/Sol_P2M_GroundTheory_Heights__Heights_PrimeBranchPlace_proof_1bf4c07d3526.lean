-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimeBranchPlace_proof_1bf4c07d3526
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:14:17.769834+00:00
-- url     : https://prove2.me/submissions/53dfa92c-be7e-4fbd-8e39-2c2fa3e3b9d5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeBranchPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeBranchDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCurveBranchOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimeBranchPlace
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelExists_proof_269d895ff472


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
namespace GroundTheory.Heights₂.Heights
namespace PrimeBranchPlace
theorem _root_.solution (hD : PrimeBranchDimOne.Statement) (hL : IndefiniteRowSideFullHecke.ComplexSets.BranchLift.Statement)
    (hA : NormalModelPlace.Statement) (hO : NormalCurveBranchOrder.Statement) : PrimeBranchPlace.Statement := by
  intro n J q c hJ hdim
  have hdim1 := hD n J q c hJ hdim
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨Γ, hΓd, hΓ, -⟩ := hL n 1 J q M c hJ hdim1
  have hr := c.radius_pos
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball 0 c.radius := Metric.mem_ball_self hr

  have hinj : Set.InjOn Γ (Metric.ball 0 c.radius) := fun a ha b hb hab ↦
    c.injOn ha hb (by rw [← (hΓ a ha).2, ← (hΓ b hb).2, hab])
  obtain ⟨P, hP⟩ := hA n J q M (Γ 0) hJ (hΓ 0 h0).1 ((hΓ 0 h0).2.trans c.map_zero)
  refine ⟨P, fun f ↦ ?_⟩
  rw [hP f, hO n J M (Γ 0) c.radius Γ hJ hdim1 hr hΓd hinj (fun τ hτ ↦ (hΓ τ hτ).1) rfl]

  unfold branchOrder
  apply analyticOrderAt_congr
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ
  have hτ' : (fun _ ↦ τ : Fin 1 → ℂ) ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
    rw [mem_ball_zero_iff] at hτ ⊢
    exact (pi_norm_const_le τ).trans_lt hτ
  rw [eval_rename, ← (hΓ _ hτ').2]
  rfl
end PrimeBranchPlace
end GroundTheory.Heights₂.Heights
