-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_rank_8d1ca699d468
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:53.740165+00:00
-- url     : https://prove2.me/submissions/dbfc0d24-2598-4e8a-9305-cbf1d2708db3

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
theorem _root_.solution (K : Type*) [Field K] [NumberField K] (x : Fin 2) :
    (HermitianBundle.standard K 2).rank (coordLines K x) = 1 := by
  change Module.finrank (𝓞 K) (LinearMap.range (LinearMap.single (𝓞 K) (fun _ : Fin 2 => 𝓞 K) x)) = 1
  have hinj : Function.Injective (LinearMap.single (𝓞 K) (fun _ : Fin 2 => 𝓞 K) x) := by
    intro a b h; simpa using congrFun h x
  rw [← (LinearEquiv.ofInjective _ hinj).finrank_eq, Module.finrank_self]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
