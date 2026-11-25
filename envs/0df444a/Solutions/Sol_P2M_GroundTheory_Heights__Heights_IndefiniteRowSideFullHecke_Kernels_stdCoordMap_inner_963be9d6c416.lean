-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_inner_963be9d6c416
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:29:41.551921+00:00
-- url     : https://prove2.me/submissions/cfde1b58-ca3f-4443-ac7e-74e0723a5f81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_apply_c8aca4d18fef

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
theorem _root_.solution (K : Type*) [Field K] [NumberField K] (n : ℕ) (σ : K →+* ℂ)
    (v w : Fin n → 𝓞 K) :
    ((HermitianBundle.standard K n).metric.form σ).inner
        ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w) =
      star (embVec σ (stdCoordMap K n v)) ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ
        embVec σ (stdCoordMap K n w)) := by
  refine (HermitianMetric.standard_inner K (Fin n) σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] v)
    ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] w)).trans ?_
  rw [Matrix.one_mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [standardCoord_tmul, standardCoord_tmul]
  simp [embVec, stdCoordMap_apply, ComplexAt.ofComplex]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
