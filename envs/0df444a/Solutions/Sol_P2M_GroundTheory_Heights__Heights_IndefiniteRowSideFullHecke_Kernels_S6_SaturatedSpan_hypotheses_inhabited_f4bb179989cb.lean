-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_SaturatedSpan_hypotheses_inhabited_f4bb179989cb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:05:47.098178+00:00
-- url     : https://prove2.me/submissions/774580f9-8b8d-482f-887b-657389398f08

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_injective_475068be98b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_standardFlag_saturated_e86c126ee556


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
open scoped nonZeroDivisors
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.SaturatedSpan
theorem _root_.solution :
    Function.Injective (stdCoordMap ℚ 2) ∧
      ∀ (t : 𝓞 ℚ) (x : Fin 2 → 𝓞 ℚ), t ≠ 0 → t • x ∈ LinearMap.range (firstIncl ℚ) →
        x ∈ LinearMap.range (firstIncl ℚ) :=
  ⟨stdCoordMap_injective ℚ 2, fun t x ht hx =>
    standardFlag_saturated (K := ℚ) 1 t x ht hx⟩
end S6.SaturatedSpan
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
