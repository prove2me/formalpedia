-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_genIndex_span_smul_9c4ec3729066
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:18:27.640887+00:00
-- url     : https://prove2.me/submissions/085070a1-e5f2-4eef-81d7-13cfe560171f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CardQuotientEqGenIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_genIndex_map_be39f3dbc967
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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {N r : ℕ}
    (u : Fin r → Fin N → K) (hu : LinearIndependent K u) (c : K) (hc : c ≠ 0) :
    genIndex (Submodule.span (𝓞 K) (Set.range u)).toAddSubgroup
        (Submodule.span (𝓞 K) (Set.range fun i => c • u i)).toAddSubgroup =
      |((Algebra.norm ℚ c : ℚ) : ℝ)| ^ r := by
  let φ : (Fin r → K) →ₗ[𝓞 K] (Fin N → K) :=
    (Fintype.linearCombination K u).restrictScalars (𝓞 K)
  have hφx : ∀ x, φ x = ∑ i, x i • u i := fun x => Fintype.linearCombination_apply K u x
  have hφ : Function.Injective φ := by
    intro x y hxy
    rw [hφx, hφx] at hxy
    have h0 : ∑ i, (x - y) i • u i = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hxy, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hu _ h0 i)
  have hstd := LinesStdIndexDet.full K r (c • (1 : Matrix (Fin r) (Fin r) K))
    (by rw [det_smul, det_one, mul_one]; exact pow_ne_zero _ hc)
  have e1 : (⇑φ ∘ fun j : Fin r => (Pi.single j 1 : Fin r → K)) = u := by
    funext j
    show Fintype.linearCombination K u (Pi.single j 1) = u j
    rw [Fintype.linearCombination_apply_single, one_smul]
  have e2 : (⇑φ ∘ fun j : Fin r => (c • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ Pi.single j 1) =
      fun i => c • u i := by
    funext j
    show Fintype.linearCombination K u ((c • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ Pi.single j 1) =
      c • u j
    rw [Matrix.smul_mulVec, one_mulVec, map_smul, Fintype.linearCombination_apply_single,
      one_smul]
  have hB : Submodule.span (𝓞 K) (Set.range u) = (stdLattice K r).map φ := by
    rw [stdLattice, Submodule.map_span, ← Set.range_comp, e1]
  have hC : Submodule.span (𝓞 K) (Set.range fun i => c • u i) = (Submodule.span (𝓞 K)
      (Set.range fun j => (c • (1 : Matrix (Fin r) (Fin r) K)) *ᵥ Pi.single j 1)).map φ := by
    rw [Submodule.map_span, ← Set.range_comp, e2]
  rw [hB, hC, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    S6.MatrixSubDegree.genIndex_map _ hφ, hstd, det_smul, det_one, mul_one, Fintype.card_fin,
    map_pow, Rat.cast_pow, abs_pow]
end S6.MatrixSubDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
