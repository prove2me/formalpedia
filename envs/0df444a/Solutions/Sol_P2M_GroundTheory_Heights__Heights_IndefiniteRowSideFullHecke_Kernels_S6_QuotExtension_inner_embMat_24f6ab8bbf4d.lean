-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_QuotExtension_inner_embMat_24f6ab8bbf4d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:49.989719+00:00
-- url     : https://prove2.me/submissions/4d666a29-6df3-4a40-bbf1-cb24d2500b85

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
theorem _root_.solution {n : ℕ} (h : Matrix (Fin n) (Fin n) ℂ) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    (u : ι → Fin n → K) (w w' : ι → ℂ) :
    star (embMat σ u *ᵥ w) ⬝ᵥ (h *ᵥ (embMat σ u *ᵥ w')) = star w ⬝ᵥ (gramAt h σ u *ᵥ w') := by
  rw [star_mulVec, ← dotProduct_mulVec, gramAt_eq, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels.S6.QuotExtension
