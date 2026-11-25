-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_proof_dce2c122fc18
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:53:20.563849+00:00
-- url     : https://prove2.me/submissions/192ae74b-ffa2-4e62-bd70-32fcf58ca7c4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CardQuotientEqGenIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_genIndex_trans_a90d09096126
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_exists_smul_mem_5d05ed05ea3c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_finrank_satSub_9140233d2de2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_log_gramDet_d03f3f69f313
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_genIndex_span_smul_9c4ec3729066
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_card_quotient_eq_genIndex_3dda1e5397e8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_card_quotient_pos_b52194926540
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianBundle_degree_eq_of_linearIndependent_05efcbd2008c
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
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.MatrixSubDegree
theorem _root_.solution : S6.MatrixSubDegree.Statement := by
  intro K _ _ N M _ H hH hconj hspan r u hu
  obtain ⟨t, ht, htM⟩ := S6.MatrixSubDegree.exists_smul_mem M hspan u
  have hτ : algebraMap (𝓞 K) K t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ht
  have hfW : ∀ i, algebraMap (𝓞 K) K t • u i ∈ Submodule.span K (Set.range u) :=
    fun i => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let s : Fin r → satSub M u := fun i => ⟨⟨algebraMap (𝓞 K) K t • u i, htM i⟩, hfW i⟩
  let L : satSub M u →ₗ[𝓞 K] (Fin N → K) := M.subtype ∘ₗ (satSub M u).subtype
  have hL : Function.Injective L := by
    intro x y h
    exact Subtype.ext (Subtype.ext h)
  have hLs : ⇑L ∘ s = fun i => algebraMap (𝓞 K) K t • u i := rfl
  have hs : LinearIndependent (𝓞 K) s := by
    refine LinearIndependent.of_comp L ?_
    rw [hLs]
    exact (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr
      (hu.units_smul fun _ => Units.mk0 _ hτ)
  have hrank : (matrixBundle M H hH hconj).rank (satSub M u) = r :=
    S6.MatrixSubDegree.finrank_satSub M u hu s hs
  refine ⟨hrank, ?_⟩
  have hcard : Fintype.card (Fin r) = (matrixBundle M H hH hconj).rank (satSub M u) := by
    rw [Fintype.card_fin, hrank]
  rw [(matrixBundle M H hH hconj).degree_eq_of_linearIndependent (satSub M u) hs hcard]
  have hlog := fun σ => S6.MatrixSubDegree.log_gramDet M H hH hconj u hu _ hτ
    (fun i => (s i : M)) (fun i => rfl) σ
  simp_rw [hlog]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    LinesProductFormula.full K _ hτ]

  have hA : M ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K) =
      (⊤ : Submodule (𝓞 K) (satSub M u)).map L := by
    rw [Submodule.map_top, LinearMap.range_comp, Submodule.range_subtype, satSub,
      Submodule.map_comap_subtype]
  have hC : Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i) =
      (Submodule.span (𝓞 K) (Set.range s)).map L := by
    rw [Submodule.map_span, ← Set.range_comp, hLs]
  have hpos := S6.MatrixSubDegree.card_quotient_pos (satSub M u) s hs hrank
  rw [S6.MatrixSubDegree.card_quotient_eq_genIndex (satSub M u) _ L hL, ← hA, ← hC] at hpos
  erw [S6.MatrixSubDegree.card_quotient_eq_genIndex (satSub M u) _ L hL]
  rw [← hA]
  erw [← hC]
  have hBC := S6.MatrixSubDegree.genIndex_span_smul u hu _ hτ
  have hN : |((Algebra.norm ℚ (algebraMap (𝓞 K) K t) : ℚ) : ℝ)| ≠ 0 := by
    rw [abs_ne_zero, Rat.cast_ne_zero, Algebra.norm_ne_zero_iff]; exact hτ
  have hCA : (Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i)).toAddSubgroup ≤
      (M ⊓ (Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).toAddSubgroup := by
    rw [Submodule.toAddSubgroup_le, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨htM i, hfW i⟩
  have hCB : (Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i)).toAddSubgroup ≤
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup := by
    rw [Submodule.toAddSubgroup_le, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show algebraMap (𝓞 K) K t • u i ∈ Submodule.span (𝓞 K) (Set.range u)
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ t (Submodule.subset_span ⟨i, rfl⟩)
  have hrel : (Submodule.span (𝓞 K) (Set.range fun i => algebraMap (𝓞 K) K t • u i)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup ≠ 0 := by
    intro h0
    apply pow_ne_zero r hN
    rw [← hBC, genIndex, h0, Nat.cast_zero, zero_div]
  have htrans := S6.MatrixSubDegree.genIndex_trans hCA hCB hrel
  rw [htrans, hBC] at hpos ⊢
  have hAB := left_ne_zero_of_mul hpos.ne'
  rw [Real.log_mul hAB (pow_ne_zero _ hN), Real.log_pow, subDegree]
  ring
end S6.MatrixSubDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
