-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_gramAt_smul_2ed8af291ccc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:09:48.10941+00:00
-- url     : https://prove2.me/submissions/c1a90e95-4dd2-4d61-a184-a5a472781f86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CardQuotientEqGenIndex

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
theorem _root_.solution {K : Type} [Field K] {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ)
    (σ : K →+* ℂ) {ι : Type*} [Fintype ι] (u : ι → Fin N → K) (c : K) :
    gramAt h σ (fun i => c • u i) = ((‖σ c‖ ^ 2 : ℝ) : ℂ) • gramAt h σ u := by
  have he : ∀ v : Fin N → K, embVec σ (c • v) = σ c • embVec σ v := fun v => by
    funext k; simp [embVec]
  ext a b
  simp only [gramAt, he, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    Matrix.smul_apply, RCLike.star_def, ← mul_assoc]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
end S6.MatrixSubDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
