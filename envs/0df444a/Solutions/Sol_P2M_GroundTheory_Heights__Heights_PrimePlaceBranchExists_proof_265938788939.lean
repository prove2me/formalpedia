-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PrimePlaceBranchExists_proof_265938788939
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:45.252098+00:00
-- url     : https://prove2.me/submissions/26698793-6203-4475-a3de-70c59a7ab826

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimePlaceBranchExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPointOfPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelProjectionLocallyInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimePlaceBranchExists
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_NormalModelExists_proof_269d895ff472
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalDimDomain_proof_aafc8deef599
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MaximalIdealHeightFG_proof_60a444887d99
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_curveLocalRing_subsingleton_6e4911beb75a


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
namespace PrimePlaceBranchExists
theorem _root_.solution (hA : NormalModelPointOfPlace.Statement) (hB : NormalModelDisc.Statement)
    (hC : NormalModelProjectionLocallyInjective.Statement) (hO : NormalCurveBranchOrder.Statement) :
    PrimePlaceBranchExists.Statement := by
  intro n J q hJ hdim P

  have hq : q ∈ zeroSet J := by
    by_contra h
    have := curveLocalRing_subsingleton J q h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : ℕ) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  obtain ⟨e, he⟩ : ∃ e : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = e := by
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
      ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d at h0 hle ⊢
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        exfalso
        simp only [not_le.2 (show ((n : ℕ) : WithBot ℕ∞) < ((⊤ : ℕ∞) : WithBot ℕ∞) from
          WithBot.coe_lt_coe.2 (ENat.natCast_lt_top n))] at hle
      | coe e => exact ⟨e, rfl⟩
  have hloc : ringKrullDim (curveLocalRing J q) = (e : ℕ) := LocalDimDomain.proof n e J hJ he q hq
  have hdim1 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) := by
    rw [he]
    rw [hloc] at hdim
    exact_mod_cast hdim
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨w, hw, hwq, hord⟩ := hA n J q M hJ P
  obtain ⟨r, hr, φ, hφd, hφi, hφm, hφ0⟩ := hB n J M w hJ hdim1 hw
  obtain ⟨U, hU, hUi⟩ := hC n J M w hJ hdim1 hw

  have hcont : ContinuousAt φ 0 := hφd.continuousOn.continuousAt (Metric.ball_mem_nhds 0 hr)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 (hcont.preimage_mem_nhds (hφ0 ▸ hU))
  have hρ : 0 < min r ε := lt_min hr hε
  have hsub : Metric.ball (0 : Fin 1 → ℂ) (min r ε) ⊆ Metric.ball 0 r :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsubU : ∀ t ∈ Metric.ball (0 : Fin 1 → ℂ) (min r ε), φ t ∈ U := fun t ht ↦
    hεU (Metric.ball_subset_ball (min_le_right _ _) ht)
  let ν : VarBranch J 1 q :=
    { radius := min r ε, radius_pos := hρ, toFun := fun t i ↦ φ t (Sum.inl i),
      differentiableOn := differentiableOn_pi.2 fun i ↦ differentiableOn_pi.1 (hφd.mono hsub) (Sum.inl i),
      injOn := fun a ha b hb hab ↦ hφi (hsub ha) (hsub hb)
        (hUi ⟨hφm (hsub ha), hsubU a ha⟩ ⟨hφm (hsub hb), hsubU b hb⟩ hab),
      map_zero := by
        funext i
        rw [hφ0]
        exact congrFun hwq i,
      mapsTo := fun t ht g hg ↦ by
        have hg' : rename Sum.inl g ∈ M.ideal := Ideal.mem_comap.1 (M.comap_eq.symm ▸ hg)
        have h := hφm (hsub ht) _ hg'
        rw [eval_rename] at h
        exact h }
  refine ⟨ν, fun f ↦ ?_⟩
  rw [hord f, hO n J M w (min r ε) φ hJ hdim1 hρ (hφd.mono hsub) (hφi.mono hsub) (fun t ht ↦ hφm (hsub ht)) hφ0]
  unfold branchOrder
  simp only [eval_rename]
  rfl
end PrimePlaceBranchExists
end GroundTheory.Heights₂.Heights
