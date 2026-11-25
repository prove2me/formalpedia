-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_gramAt_smul_193511ca268a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:08:24.817668+00:00
-- url     : https://prove2.me/submissions/e54297c9-7051-4512-9912-075e854d6fdc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_SpanEqTopSmul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
theorem _root_.solution {K : Type*} [Field K] {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ)
    {ι : Type*} (u : ι → Fin n → K) (c : K) :
    gramAt h σ (fun a => c • u a) = ((‖σ c‖ ^ 2 : ℝ) : ℂ) • gramAt h σ u := by
  have he : ∀ v : Fin n → K, embVec σ (c • v) = σ c • embVec σ v := fun v => by
    funext k
    simp [embVec]
  ext a b
  simp only [gramAt, he, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, Complex.star_def, Complex.mul_conj']
  push_cast
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
