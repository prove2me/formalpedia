-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_standard_inner_single_ne_650d14c0e8b4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:08.731815+00:00
-- url     : https://prove2.me/submissions/5e03c3c7-7fe9-4dc4-82d0-40b44b31561e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe

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
open NumberField TensorProduct GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
theorem _root_.solution (K : Type*) [Field K] [NumberField K] (σ : K →+* ℂ)
    (x y : Fin 2) (hxy : x ≠ y) (a b : 𝓞 K) :
    ((HermitianMetric.standard K (Fin 2)).form σ).inner
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (Pi.single x a : Fin 2 → 𝓞 K))
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] (Pi.single y b : Fin 2 → 𝓞 K)) = 0 := by
  rw [HermitianMetric.standard_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [standardCoord_tmul, standardCoord_tmul]
  by_cases hi : i = x
  · subst hi
    simp [hxy]
  · simp [Pi.single_apply, hi]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
