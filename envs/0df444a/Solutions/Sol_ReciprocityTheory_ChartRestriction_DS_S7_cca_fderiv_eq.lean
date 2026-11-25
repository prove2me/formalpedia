-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.cca_fderiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:23.377913+00:00
-- url     : https://prove2.me/submissions/979d961a-0eec-43d4-85bf-91b51e1026ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Metric Set Filter Topology MeasureTheory Complex
open scoped ContDiff Real
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution [CompleteSpace E] {F : X → E} {U : Set X} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {z u : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : ∀ t ∈ closedBall (0 : ℂ) ρ, z + t • u ∈ U) :
    fderiv ℂ F z u = (2 * π * I)⁻¹ •
      ∫ θ in (0 : ℝ)..2 * π, ccaKappa ρ θ • F (z + circleMap 0 ρ θ • u) := by
  have hU' : IsOpen {t : ℂ | z + t • u ∈ U} :=
    hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hg : DifferentiableOn ℂ (fun t : ℂ => F (z + t • u)) {t : ℂ | z + t • u ∈ U} :=
    hF.comp (((differentiable_id.smul_const u).const_add z).differentiableOn) (fun t ht => ht)
  have hz : z ∈ U := by simpa using hsub 0 (mem_closedBall_self hρ.le)
  have hderiv : deriv (fun t : ℂ => F (z + t • u)) 0 = fderiv ℂ F z u := by
    have hF' : HasFDerivAt F (fderiv ℂ F z) (z + (0 : ℂ) • u) := by
      simpa using (hF.differentiableAt (hU.mem_nhds hz)).hasFDerivAt
    have hl : HasDerivAt (fun t : ℂ => z + t • u) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const u).const_add z
    exact (hF'.comp_hasDerivAt (0 : ℂ) hl).deriv
  rw [← hderiv, ← two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU'
    (fun t ht => hsub t ht) hg (mem_ball_self hρ)]
  congr 1
  simp only [circleIntegral]
  refine intervalIntegral.integral_congr (fun θ _ => ?_)
  simp only [ccaKappa, smul_smul, one_div]
end ReciprocityTheory.ChartRestriction.DS.S7
