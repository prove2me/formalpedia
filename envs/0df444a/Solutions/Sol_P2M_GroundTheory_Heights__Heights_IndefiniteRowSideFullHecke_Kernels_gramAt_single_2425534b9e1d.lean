-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_gramAt_single_2425534b9e1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:35.037742+00:00
-- url     : https://prove2.me/submissions/0cbb6524-9f58-4f81-addf-742ce7f0e2c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ReMulOfPos

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
theorem _root_.solution {K : Type*} [Field K] {k : ℕ} (h : Matrix (Fin k) (Fin k) ℂ) (σ : K →+* ℂ) :
    gramAt h σ (fun j : Fin k => (Pi.single j 1 : Fin k → K)) = h := by
  have he : ∀ j : Fin k, embVec σ (Pi.single j 1 : Fin k → K) = Pi.single j 1 := fun j => by
    funext i
    by_cases hij : i = j
    · subst hij; simp [embVec]
    · simp [embVec, hij]
  ext a b
  simp [gramAt, he, mulVec_single, single_dotProduct]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
