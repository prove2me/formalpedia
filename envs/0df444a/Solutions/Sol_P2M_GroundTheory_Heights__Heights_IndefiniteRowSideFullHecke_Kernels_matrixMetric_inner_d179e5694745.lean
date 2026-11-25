-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_matrixMetric_inner_d179e5694745
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:41:59.238473+00:00
-- url     : https://prove2.me/submissions/55430c9c-c668-4939-abde-b834f6f739c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_CommonDenominator
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects

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
variable {K : Type} [Field K] [NumberField K]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
theorem _root_.solution {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (H : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (hconj : ∀ σ, H (conjugate σ) = (H σ).map (starRingEnd ℂ)) (σ : K →+* ℂ) (x y : Fibre σ M) :
    ((matrixMetric M H hH hconj).form σ).inner x y =
      star (latticeCoord σ M x) ⬝ᵥ (H σ *ᵥ latticeCoord σ M y) := rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
