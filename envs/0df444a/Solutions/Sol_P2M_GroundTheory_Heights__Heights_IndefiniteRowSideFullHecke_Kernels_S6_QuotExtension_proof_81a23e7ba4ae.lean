-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_proof_81a23e7ba4ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:24:37.177807+00:00
-- url     : https://prove2.me/submissions/4cfee426-ce02-40d0-a323-a59f61c33fdd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemIdealLattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_schur_inner_c8f7618261dc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_inner_embMat_24f6ab8bbf4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_gramAt_mulVec_apply_28178724728b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_coord_decomp_f25ef847aa3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_orth_sub_d589be79082f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_sumBasis_apply_2327b92b9453
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_ker_coordProj_eba1c16731d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesCoordDet_full_c35610a5b491
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesCoordImage_full_39a2e8bb2bcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesDiagGram_full_8ff11ddb230b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesExtendBasis_full_63f55d25134d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesFischer_full_deb5581a4d66
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexDet_full_b60a8a3c7864
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexMono_full_6f6f30f807ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexPi_full_33ed3f72d0c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexTrans_full_3ca845fd298c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramChange_full_dcb0a61411bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramDetChange_full_12fe0540b59d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramFischerBound_full_1469f2c017cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramPosDef_full_e43342dbfc82
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealIndexPos_full_4f9c5f06aec4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealLatticeFG_full_1aee04d7db78
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealStdIndex_full_42daaad5b08f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIsLattice_full_bf47e659fe20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesLatticeBasis_full_7e8167254293
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesLineDegree_full_c44e0f792b53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProductFormula_full_ff39a65d05f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProjIndexLower_full_1df55b623de3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProjLattice_full_509886f65659
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotDegreeBound_full_f1f9aab9b801
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotGramLog_full_1c29f5d3742d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndexLog_full_349909a2722b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndexSplit_full_f051c7119c9e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndex_full_e73217d08651
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesStdIndexDet_full_f76414530167
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesStdPi_full_9d1e83483f6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrthogonalLines_full_ff0437c876fb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder
noncomputable section
open S6.QuotExtension
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.QuotExtension
theorem _root_.solution : S6.QuotExtension.Statement := by
  intro K _ _ n a d hd hc ha m k b c hli hmk
  refine ⟨{ incl := (subLattice a b).subtype
            proj := quotProj a b c hli hmk
            incl_injective := (subLattice a b).injective_subtype
            proj_surjective := LinearMap.submoduleMap_surjective _ _
            exact := ?_
            incl_isometric := fun σ x y => rfl
            proj_coisometric := ?_ }, rfl, rfl⟩
  · show ∀ y : idealLattice a, quotProj a b c hli hmk y = 0 ↔ y ∈ Set.range (subLattice a b).subtype
    intro y
    have hker := KLinesQuotIndex.ker_coordProj (sumBasis b c hli hmk)
    have hr : (fun i => sumBasis b c hli hmk (Sum.inl i)) = b :=
      funext fun i => by rw [sumBasis_apply]; rfl
    rw [hr] at hker
    have h1 : quotProj a b c hli hmk y = 0 ↔
        coordProj (sumBasis b c hli hmk) (y : Fin n → K) = 0 := by
      rw [← Submodule.coe_eq_zero]
      exact Iff.rfl
    rw [h1, ← LinearMap.mem_ker, hker]
    constructor
    · intro h
      exact ⟨⟨y, h⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      exact w.2
  · intro σ x y _ hy
    obtain ⟨β, hx⟩ := coord_decomp a b c hli hmk σ x
    obtain ⟨β', hy'⟩ := coord_decomp a b c hli hmk σ y
    have hG := LinesGramPosDef.full K n _ σ _ _ (diagMetric_posDef hd σ) hli
    have hA : IsUnit (gramAt (diagMetric d σ) σ (Sum.elim b c)).toBlocks₁₁.det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (hG.submatrix Sum.inl_injective).isUnit
    change star (latticeCoord σ (quotLattice a b c hli hmk) _) ⬝ᵥ
        (schurMetric d b c σ *ᵥ latticeCoord σ (quotLattice a b c hli hmk) _) =
      star (latticeCoord σ (idealLattice a) x) ⬝ᵥ
        (diagMetric d σ *ᵥ latticeCoord σ (idealLattice a) y)
    rw [hx, hy', inner_embMat]
    refine (schur_inner _ hA _ _ _ _ fun i => ?_).symm
    rw [gramAt_mulVec_apply]
    exact (congrArg (fun v => star (embVec σ (b i)) ⬝ᵥ (diagMetric d σ *ᵥ v)) hy').symm.trans
      (orth_sub ha hd hc b σ y hy i)
end S6.QuotExtension
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
