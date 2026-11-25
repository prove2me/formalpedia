-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotDegree_proof_9f64677a504a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:36.462141+00:00
-- url     : https://prove2.me/submissions/1b42a976-eef4-45e5-ab6a-677d588e865e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ReMulOfPos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_gramAt_single_2425534b9e1d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_re_mul_of_pos_8ae9e150c1fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_sumBasis_apply_2327b92b9453
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_basis_inr_8d05f19318c1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesProjLattice_coordProj_surjective_e0159a2963b4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesQuotIndex_coordProj_surjective_59e6542cb5fd
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
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.QuotDegree
theorem _root_.solution : S6.QuotDegree.Statement := by
  intro K _ _ n a d ha hd m k b c hli hmk
  set B := sumBasis b c hli hmk
  have hb : (fun i => B (Sum.inl i)) = b := funext fun i => by simp [B, sumBasis_apply]
  have hc : coordProj B ∘ c = fun j : Fin k => (Pi.single j 1 : Fin k → K) := funext fun j => by
    have : c j = B (Sum.inr j) := by simp [B, sumBasis_apply]
    rw [Function.comp_apply, this, KLinesProjLattice.coordProj_basis_inr]
  refine ⟨?_, ?_⟩
  · rw [quotLattice, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image,
      (LinesIdealLatticeFG.full K n a ha).2, Submodule.map_top, LinearMap.range_eq_top]
    exact KLinesQuotIndex.coordProj_surjective B
  · have hspan : Submodule.span K (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K)) = ⊤ := by
      have h : (Set.range fun j : Fin k => (Pi.single j 1 : Fin k → K)) =
          Set.range (Pi.basisFun K (Fin k)) := by
        congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
      rw [h]; exact (Pi.basisFun K (Fin k)).span_eq
    have hidx := LinesQuotIndex.full K n m k B (idealLattice a) c
    rw [hb, hc] at hidx
    unfold subDegree quotDegree
    rw [hspan, Submodule.restrictScalars_top, inf_top_eq, hidx]
    congr 2
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [gramAt_single]
    set G := gramAt (diagMetric d σ) σ (Sum.elim b c)
    have hG : G.PosDef := LinesGramPosDef.full K n _ σ _ _ (diagMetric_posDef hd σ) hli
    have hA : G.toBlocks₁₁.PosDef := hG.submatrix Sum.inl_injective
    have hS : (schurMetric d b c σ).PosDef := schurMetric_posDef hd hli σ
    have hbb : gramAt (diagMetric d σ) σ b = G.toBlocks₁₁ := rfl
    have : Invertible G.toBlocks₁₁ := hA.isUnit.invertible
    have hdet : G.det = G.toBlocks₁₁.det * (schurMetric d b c σ).det := by
      conv_lhs => rw [← fromBlocks_toBlocks G]
      rw [det_fromBlocks₁₁, invOf_eq_nonsing_inv]
      rfl
    have hApos := hA.det_pos
    have hSpos := hS.det_pos
    rw [hbb, hdet, re_mul_of_pos _ hApos,
      Real.log_mul (Complex.pos_iff.mp hApos).1.ne' (Complex.pos_iff.mp hSpos).1.ne']
    ring
end S6.QuotDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
