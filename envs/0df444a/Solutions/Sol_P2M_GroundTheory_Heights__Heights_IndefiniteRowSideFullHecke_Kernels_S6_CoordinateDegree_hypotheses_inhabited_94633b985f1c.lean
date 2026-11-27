-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_CoordinateDegree_hypotheses_inhabited_94633b985f1c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:31.4702+00:00
-- url     : https://prove2.me/submissions/f4abf35e-7851-4d3c-bac5-4502fb0d648d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_injective_475068be98b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_span_1f6bd7367cc3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_inner_963be9d6c416

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
namespace S6.CoordinateDegree
theorem _root_.solution :
    Function.Injective (stdCoordMap ℚ 2) ∧
      Submodule.span ℚ (LinearMap.range (stdCoordMap ℚ 2) : Set (Fin 2 → ℚ)) = ⊤ ∧
      (∀ (σ : ℚ →+* ℂ) (v w : Fin 2 → 𝓞 ℚ),
        ((HermitianBundle.standard ℚ 2).metric.form σ).inner
            ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 ℚ] w) =
          star (embVec σ (stdCoordMap ℚ 2 v)) ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ
            embVec σ (stdCoordMap ℚ 2 w))) ∧
      LinearIndependent ℚ (Pi.basisFun ℚ (Fin 2)) ∧
      (⊤ : Submodule (𝓞 ℚ) (Fin 2 → 𝓞 ℚ)).map (stdCoordMap ℚ 2) =
        LinearMap.range (stdCoordMap ℚ 2) ⊓
          (Submodule.span ℚ (Set.range (Pi.basisFun ℚ (Fin 2)))).restrictScalars (𝓞 ℚ) := by
  refine ⟨stdCoordMap_injective ℚ 2, stdCoordMap_span ℚ 2, stdCoordMap_inner ℚ 2,
    (Pi.basisFun ℚ (Fin 2)).linearIndependent, ?_⟩
  rw [(Pi.basisFun ℚ (Fin 2)).span_eq, Submodule.restrictScalars_top, inf_top_eq,
    Submodule.map_top]
end S6.CoordinateDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
