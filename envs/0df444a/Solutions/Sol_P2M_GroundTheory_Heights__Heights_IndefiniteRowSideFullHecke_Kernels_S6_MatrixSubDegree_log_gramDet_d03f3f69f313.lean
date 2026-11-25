-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_log_gramDet_d03f3f69f313
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:32:34.525176+00:00
-- url     : https://prove2.me/submissions/0351949c-2a6d-4038-853b-12ee749b9f0f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CardQuotientEqGenIndex
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_gramAt_smul_2ed8af291ccc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_matrixMetric_inner_one_tmul_c11a04f23944
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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {N : ℕ}
    (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (H : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (hconj : ∀ σ, H (conjugate σ) = (H σ).map (starRingEnd ℂ)) {r : ℕ} (u : Fin r → Fin N → K)
    (hu : LinearIndependent K u) (c : K) (hc : c ≠ 0) (v : Fin r → M)
    (hv : ∀ i, (v i : Fin N → K) = c • u i) (σ : K →+* ℂ) :
    Real.log (gramDet (matrixBundle M H hH hconj).metric σ v) =
      r * (2 * Real.log ‖σ c‖) + Real.log (gramAt (H σ) σ u).det.re := by
  have hG : (gram ℂ fun i => fibreVec (matrixBundle M H hH hconj).metric σ (v i)) =
      ((‖σ c‖ ^ 2 : ℝ) : ℂ) • gramAt (H σ) σ u := by
    have e : (fun i => c • u i) = fun i => (v i : Fin N → K) := funext fun i => (hv i).symm
    rw [← S6.MatrixSubDegree.gramAt_smul, e]
    ext i j
    rw [gram_apply]
    exact matrixMetric_inner_one_tmul M H hH hconj σ (v i) (v j)
  have hD : 0 < (gramAt (H σ) σ u).det.re := by
    have := (LinesGramPosDef.full K N (H σ) σ (Fin r) u (hH σ) hu).det_pos
    exact (RCLike.pos_iff.mp this).1
  have hσc : ‖σ c‖ ≠ 0 := by
    rw [norm_ne_zero_iff, map_ne_zero]; exact hc
  simp only [GroundTheory.Heights₂.Heights.gramDet]
  rw [hG, det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Real.log_mul (pow_ne_zero _ (pow_ne_zero _ hσc)) hD.ne', Real.log_pow, Real.log_pow]
  push_cast
  ring
end S6.MatrixSubDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
