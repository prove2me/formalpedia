-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_MatrixSubDegree_genIndex_map_be39f3dbc967
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:50.572651+00:00
-- url     : https://prove2.me/submissions/3cbc7697-ee60-401a-a188-61a9b023b722

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsMore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_LinearIndependentSumElimOfExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsSmulMemFamilyOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CardQuotientEqGenIndex

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
open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors ComplexOrder
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.MatrixSubDegree
theorem _root_.solution {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    (f : G →+ G') (hf : Function.Injective f) (A B : AddSubgroup G) :
    genIndex (A.map f) (B.map f) = genIndex A B := by
  unfold genIndex
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_map_map_of_injective _ _ hf]
end S6.MatrixSubDegree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
