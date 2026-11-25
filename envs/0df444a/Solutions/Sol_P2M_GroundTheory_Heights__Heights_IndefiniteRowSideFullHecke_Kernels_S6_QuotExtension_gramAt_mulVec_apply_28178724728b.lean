-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_gramAt_mulVec_apply_28178724728b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:01:05.528233+00:00
-- url     : https://prove2.me/submissions/00ab9da1-0525-4bb9-bc7d-4bcf4d3ded54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsTer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemIdealLattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_gramAt_eq_b566515e4e1b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGramChange_gramAt_eq_5016030237f4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesGramPosDef_gramAt_eq_c14de37355de


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
theorem _root_.solution {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*}
    [Fintype ι] (u : ι → Fin n → K) (w : ι → ℂ) (s : ι) :
    (gramAt h σ u *ᵥ w) s = star (embVec σ (u s)) ⬝ᵥ (h *ᵥ (embMat σ u *ᵥ w)) := by
  rw [gramAt_eq, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [mulVec, dotProduct, conjTranspose_apply, embMat, embVec, of_apply, Pi.star_apply]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
