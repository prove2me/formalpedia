-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_UniformiserBranchSimpleZero_proof_aaa4b82d6f25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:11:10.747859+00:00
-- url     : https://prove2.me/submissions/14eb914a-3499-499c-9b1c-f4279a86ad33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserBranchSimpleZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserLocallyInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicDerivNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PointLocalRingOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUniformiserBranchSimpleZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_analyticAt_eval_disc_feccb63fcfb3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_differentiable_eval_pointLocal_327219f7cdc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isUnit_algebraMap_pointLocalRing_0914499906a4


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
open MvPolynomial Topology
namespace GroundTheory.Heights₂.Heights
namespace UniformiserBranchSimpleZero
theorem _root_.solution (hloc : UniformiserLocallyInjective.Statement)
    (hder : InjectiveHolomorphicDerivNeZero.Statement) : UniformiserBranchSimpleZero.Statement := by
  intro σ _ I w t r φ hI hic hdim ht hr hdiff hinj hmaps hw0
  have hball : ∀ {ρ : ℝ} {τ : ℂ}, τ ∈ Metric.ball (0 : ℂ) ρ →
      (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) ρ := by
    intro ρ τ hτ
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hwZ : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I := hw0 ▸ hmaps (Metric.mem_ball_self hr)
  have htw : eval w t = 0 := by
    by_contra h
    exact ht.not_isUnit (isUnit_algebraMap_pointLocalRing I w t h)
  obtain ⟨U, hU, hUinj⟩ := hloc σ I w t hI hic hdim hwZ ht
  have hφc : ContinuousAt φ 0 :=
    (hdiff.differentiableAt (Metric.ball_mem_nhds 0 hr)).continuousAt
  have hc1 : Continuous fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ) := continuous_pi fun _ ↦ continuous_id
  have hcont : ContinuousAt (fun τ : ℂ ↦ φ fun _ ↦ τ) 0 :=
    ContinuousAt.comp_of_eq (g := φ) (f := fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) hφc hc1.continuousAt rfl
  have hpre : (fun τ : ℂ ↦ φ fun _ ↦ τ) ⁻¹' U ∈ 𝓝 (0 : ℂ) :=
    hcont.preimage_mem_nhds (by rw [← hw0] at hU; exact hU)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hpre (Metric.ball_mem_nhds 0 hr))
  have hfd : DifferentiableOn ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) (Metric.ball 0 ε) :=
    (differentiable_eval_pointLocal t).comp_differentiableOn (hdiff.comp
      (differentiable_pi.2 fun _ ↦ differentiable_id).differentiableOn fun τ hτ ↦ hball (hεU hτ).2)
  have hfi : Set.InjOn (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) (Metric.ball 0 ε) := by
    intro a ha b hb hab
    have hab' := hUinj ⟨hmaps (hball (hεU ha).2), (hεU ha).1⟩ ⟨hmaps (hball (hεU hb).2), (hεU hb).1⟩ hab
    exact congrFun (hinj (hball (hεU ha).2) (hball (hεU hb).2) hab') 0
  have hd := hder _ _ Metric.isOpen_ball hfd hfi 0 (Metric.mem_ball_self hε)
  have hf0 : (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 = 0 := by
    change eval (φ 0) t = 0
    rw [hw0, htw]
  exact (analyticAt_eval_disc hr hdiff t).analyticOrderAt_eq_one_of_zero_deriv_ne_zero hf0 hd
end UniformiserBranchSimpleZero
end GroundTheory.Heights₂.Heights
