-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_proof_04c9e304ee98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:13:55.502527+00:00
-- url     : https://prove2.me/submissions/a43f28ea-f506-4a7e-b306-d9155889c508

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinPointModel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinPointModel_ringKrullDim_join_ae569ee243f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_isModelOver_iff_72f2abf14dfc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_BundleExamples_mcIdeal_eq_pointIdeal_dc408f6410cc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDim_isMultiProjPrime_pointIdeal_058978c6cf77


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord joinCoord mcMap)
open JoinPointModel
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace JoinPointModel
theorem _root_.solution : JoinPointModel.Statement := by
  intro O _ _ _ Ω _ _ K _ _ ι _ y d hW
  rw [BundleExamples.isModelOver_iff]
  refine ⟨inferInstance, ⟨?_, ?_, ?_⟩⟩
  · apply GenericProjClosureDim.isMultiProjPrime_pointIdeal
    rintro (k | u)
    · obtain ⟨j, hj⟩ := hW.multiProj.relevant k
      refine ⟨j, fun h0 => hj ?_⟩
      change y ⟨k, j⟩ = 0 at h0
      rw [pointIdeal, RingHom.mem_ker]
      simp [pointConeMap, h0]
    · exact ⟨(0 : Fin 1), by simp [joinCoord, ptCoord]⟩
  · rw [eq_bot_iff]
    intro a ha
    rw [← hW.noTorsion]
    simp only [Ideal.mem_comap, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal, pointIdeal, RingHom.mem_ker,
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, C_eq_zero] at ha ⊢
    exact ha
  · rw [BundleExamples.mcIdeal_eq_pointIdeal, ringKrullDim_join, hW.dim, Fintype.card_sum, Fintype.card_unit,
      show d + 1 + (Fintype.card K + 1) = (d + 1 + Fintype.card K) + 1 by omega]
    norm_cast
end JoinPointModel
end GroundTheory.Heights₂.Heights.NumbersDVR
