-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_exists_ne_zero_6aec105870c0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:34:47.060832+00:00
-- url     : https://prove2.me/submissions/3c1a1238-6cce-4fb7-8406-d9e46b39da44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsConeTrdegFnField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinTwoModels
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isModelOver_iff_72f2abf14dfc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_mcIdeal_eq_pointIdeal_dc408f6410cc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_FieldNumbers_coeff_coeffForm_479fc53ecb0b



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcIdeal joinCoord fnField)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels
theorem _root_.solution {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    {d : ℕ} (h : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O y) d) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  classical
  rw [BundleExamples.mcIdeal_eq_pointIdeal, BundleExamples.isModelOver_iff] at h
  obtain ⟨j, hj⟩ := h.2.multiProj.relevant k
  refine ⟨j, fun h0 => hj ?_⟩
  rw [pointIdeal, RingHom.mem_ker]
  simp [pointConeMap, h0]
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels
