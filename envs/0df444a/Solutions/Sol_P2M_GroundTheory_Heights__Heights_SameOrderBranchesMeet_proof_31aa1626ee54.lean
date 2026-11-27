-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SameOrderBranchesMeet_proof_31aa1626ee54
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:08:14.630873+00:00
-- url     : https://prove2.me/submissions/0b65363e-af11-4878-8acd-9f3cc2aac277

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrderBranchesMeet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInCurveComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSameOrdersLiftCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchLift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSameOrderBranchesMeet
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarBranch_eventually_mem_zeroSet_2d02523e1957
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
namespace SameOrderBranchesMeet
theorem _root_.solution (hC : BranchInCurveComponent.Statement) (hO : SameOrdersLiftCentre.Statement)
    (hL : IndefiniteRowSideFullHecke.ComplexSets.BranchLift.Statement) : SameOrderBranchesMeet.Statement := by
  intro n I q c c' _ hdim hord
  obtain ⟨J, hJmin, hJdim, hev⟩ := hC n I q c hdim
  have hJ : J.IsPrime := hJmin.1.1
  have htop : ∀ f ∈ J, branchOrder c f = ⊤ := fun f hf ↦ by
    refine analyticOrderAt_eq_top.2 ?_
    have hι : Tendsto (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (𝓝 0) (𝓝 0) :=
      (continuous_pi fun _ ↦ continuous_id).tendsto' _ _ rfl
    filter_upwards [hι.eventually hev] with τ hτ using hτ f hf
  have hev' := c'.eventually_mem_zeroSet J fun f hf ↦ (hord f).symm.trans (htop f hf)
  obtain ⟨ε, hε, hεJ⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨ε', hε', hεJ'⟩ := Metric.eventually_nhds_iff_ball.1 hev'
  let γ := c.restrictInto J ε hε hεJ
  let γ' := c'.restrictInto J ε' hε' hεJ'
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨Γ, hΓd, hΓ, -⟩ := hL n 1 J q M γ hJ hJdim
  obtain ⟨Γ', hΓ'd, hΓ', hΓ'o⟩ := hL n 1 J q M γ' hJ hJdim
  have hw : Γ 0 = Γ' 0 := hO n J q M γ γ' Γ Γ' hJ hJdim hΓd hΓ hΓ'd hΓ' hord
  obtain ⟨U, hUo, hU⟩ := hΓ'o _ subset_rfl Metric.isOpen_ball
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball 0 γ.radius := Metric.mem_ball_self γ.radius_pos
  have hΓ0U : Γ 0 ∈ U := by
    rw [hw]
    exact (hU ▸ Set.mem_image_of_mem Γ' (Metric.mem_ball_self γ'.radius_pos)).2
  have hcont : ContinuousAt Γ 0 := hΓd.continuousOn.continuousAt (Metric.ball_mem_nhds 0 γ.radius_pos)
  have hnear : ∀ᶠ τ in 𝓝[≠] (0 : Fin 1 → ℂ), τ ≠ 0 ∧ τ ∈ Metric.ball 0 γ.radius ∧ Γ τ ∈ U := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 γ.radius_pos),
      nhdsWithin_le_nhds (hcont.preimage_mem_nhds (hUo.mem_nhds hΓ0U))] with τ h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨τ, hτ0, hτ, hτU⟩ := hnear.exists
  obtain ⟨τ', hτ', hτ'eq⟩ : Γ τ ∈ Γ' '' Metric.ball 0 γ'.radius := hU ▸ ⟨(hΓ τ hτ).1, hτU⟩
  have hτc : τ ∈ Metric.ball 0 c.radius := Metric.ball_subset_ball (min_le_right _ _) hτ
  refine ⟨c.toFun τ, ⟨⟨τ, hτc, rfl⟩, ⟨τ', Metric.ball_subset_ball (min_le_right _ _) hτ', ?_⟩⟩, fun hq ↦ hτ0 ?_⟩
  · have e1 := (hΓ' τ' hτ').2
    have e2 := (hΓ τ hτ).2
    rw [hτ'eq] at e1
    exact e1.symm.trans e2
  · exact c.injOn hτc (Metric.mem_ball_self c.radius_pos) (hq.trans c.map_zero.symm)
end SameOrderBranchesMeet
end GroundTheory.Heights₂.Heights
