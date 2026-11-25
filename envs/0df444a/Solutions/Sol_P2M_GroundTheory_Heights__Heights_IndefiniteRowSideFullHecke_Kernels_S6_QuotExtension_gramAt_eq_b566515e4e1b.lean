-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_gramAt_eq_b566515e4e1b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:43:42.575139+00:00
-- url     : https://prove2.me/submissions/eeafd1a5-49d1-4379-845c-d199fd32c217

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemIdealLattice

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6 GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
variable {K : Type} [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
theorem _root_.solution {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) : gramAt h σ u = (embMat σ u)ᴴ * h * embMat σ u := by
  ext s t
  simp only [gramAt, embVec, embMat, dotProduct, mulVec, Matrix.mul_apply, conjTranspose_apply,
    of_apply, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
  ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
