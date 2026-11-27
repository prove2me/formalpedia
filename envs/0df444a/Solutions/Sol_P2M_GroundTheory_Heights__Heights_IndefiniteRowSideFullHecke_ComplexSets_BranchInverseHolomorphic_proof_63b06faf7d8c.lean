-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_BranchInverseHolomorphic_proof_63b06faf7d8c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:57:34.314709+00:00
-- url     : https://prove2.me/submissions/980cace1-afe9-48a0-8e0d-beeb9e03fa21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInverseHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalRiemannExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchFillDimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalOpenMapping
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInverseOffHypersurface
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchContainsNormalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchInverseHolomorphic
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
namespace BranchInverseHolomorphic
theorem _root_.solution (hdim : BranchFillDimension.Statement)
    (hopen : NormalOpenMapping.Statement) (hreg : BranchInverseOffHypersurface.Statement)
    (hext : NormalRiemannExtension.Statement) (hirr : NormalLocallyIrreducible.Statement) :
    BranchInverseHolomorphic.Statement := by
  intro σ _ I h w k r φ B hI hIc hh hw hφd hφi hφZ hB hfill
  set Δ := Metric.ball (0 : Fin k → ℂ) r with hΔ
  have hk := hdim σ I h w k r φ B hI hh hw hφd hφi hφZ hB hfill
  set ψ : (σ → ℂ) → Fin k → ℂ := Function.invFunOn φ Δ with hψdef
  have hψφ : ∀ t ∈ Δ, ψ (φ t) = t := fun t ht => hφi.leftInvOn_invFunOn ht
  obtain ⟨O, hOo, hO⟩ := hopen σ I k Δ φ hI hIc hk Metric.isOpen_ball hφd hφi hφZ

  have hψc : ∀ z ∈ φ '' Δ, ContinuousWithinAt ψ (φ '' Δ) z := by
    rintro _ ⟨t, ht, rfl⟩
    rw [ContinuousWithinAt, hψφ t ht, tendsto_nhds]
    intro V hVo htV
    obtain ⟨O', hO'o, hO'⟩ := hopen σ I k (V ∩ Δ) φ hI hIc hk (hVo.inter Metric.isOpen_ball)
      (hφd.mono Set.inter_subset_right) (hφi.mono Set.inter_subset_right)
      (hφZ.mono_left Set.inter_subset_right)
    have hmem : φ t ∈ zeroSetIn I ∩ O' := hO' ▸ Set.mem_image_of_mem φ ⟨htV, ht⟩
    filter_upwards [inter_mem_nhdsWithin (φ '' Δ) (hO'o.mem_nhds hmem.2)] with z hz
    obtain ⟨⟨s, hs, rfl⟩, hzO'⟩ := hz
    have hs' : φ s ∈ φ '' (V ∩ Δ) := by rw [hO']; exact ⟨hφZ hs, hzO'⟩
    obtain ⟨s', hs'V, hss'⟩ := hs'
    rw [Set.mem_preimage, hψφ s hs, ← hφi hs'V.2 hs hss']
    exact hs'V.1
  obtain ⟨h', hh', hreg'⟩ := hreg σ I k hI hk
  have hψreg := hreg' Δ φ ψ Metric.isOpen_ball hφd hφi hφZ hψφ
  rw [hO] at hψreg hψc

  have hcoord : ∀ j : Fin k, ∃ g : (σ → ℂ) → ℂ, HolomorphicOnSubset g (zeroSetIn I ∩ O) ∧
      Set.EqOn g (fun z => ψ z j) ((zeroSetIn I ∩ O) \ {z | eval z h' = 0}) := by
    intro j
    refine hext σ I h' O (fun z => ψ z j) hI hIc hh' hOo ?_ ?_
    · intro z hz
      obtain ⟨U, hUo, hzU, F, hF, hFeq⟩ := hψreg z hz
      exact ⟨U, hUo, hzU, fun y => F y j, differentiableOn_pi.mp hF j,
        fun y hy => congrFun (hFeq hy) j⟩
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r)).subset ?_
      rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ φ '' Δ := by rw [hO]; exact hz.1
      obtain ⟨t, ht, rfl⟩ := hz'
      rw [Metric.mem_closedBall, dist_zero_right]
      show ‖ψ (φ t) j‖ ≤ r
      rw [hψφ t ht]
      exact (norm_le_pi_norm t j).trans (mem_ball_zero_iff.mp ht).le
  choose g hg hgeq using hcoord

  have hgψ : ∀ j, ∀ z ∈ zeroSetIn I ∩ O, g j z = ψ z j := by
    intro j z hz
    obtain ⟨B', -, hzB', hB'O, -, hdense⟩ := hirr σ I h' z hI hIc hh' hz.1 O (hOo.mem_nhds hz.2)
    set P := (zeroSetIn I ∩ B') \ {y | eval y h' = 0} with hP
    have hPsub : P ⊆ zeroSetIn I ∩ O := fun y hy => ⟨hy.1.1, hB'O hy.1.2⟩
    have : (𝓝[P] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense ⟨hz.1, hzB'⟩)
    have h1 : Tendsto (g j) (𝓝[P] z) (𝓝 (g j z)) := (((hg j).continuousWithinAt hz).mono hPsub).tendsto
    have h2 : Tendsto (fun y => ψ y j) (𝓝[P] z) (𝓝 (ψ z j)) :=
      (((continuous_apply j).continuousAt.comp_continuousWithinAt (hψc z hz)).mono hPsub).tendsto
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hgeq j ⟨hPsub hy, hy.2⟩).symm
  refine ⟨ψ, ?_, hψφ⟩
  rw [hO]
  intro z hz
  choose U hUo hzU F hF hFeq using fun j => hg j z hz
  refine ⟨⋂ j, U j, isOpen_iInter_of_finite hUo, Set.mem_iInter.mpr hzU, fun y j => F j y,
    differentiableOn_pi.mpr fun j => (hF j).mono (Set.iInter_subset _ j), fun y hy => ?_⟩
  funext j
  show ψ y j = F j y
  rw [← hgψ j y hy.1]
  exact hFeq j ⟨hy.1, Set.mem_iInter.mp hy.2 j⟩
end BranchInverseHolomorphic
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
