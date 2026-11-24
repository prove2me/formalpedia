-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_stdCoordMap_apply_c8aca4d18fef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:48.501476+00:00
-- url     : https://prove2.me/submissions/93d27a42-e848-4378-a7d2-db454230db7b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective

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
theorem _root_.solution (K : Type*) [Field K] (n : ℕ) (v : Fin n → 𝓞 K) (i : Fin n) :
    stdCoordMap K n v i = (v i : K) := rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
