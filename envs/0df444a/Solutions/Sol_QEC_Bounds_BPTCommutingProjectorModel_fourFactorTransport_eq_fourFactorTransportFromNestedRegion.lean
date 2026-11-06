-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_eq_fourFactorTransportFromNestedRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:25:19.688221+00:00
-- url     : https://prove2.me/submissions/0bf34d2f-5bba-4c4c-81de-742f4c188595

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_ext


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    M.fourFactorTransport region = M.fourFactorTransportFromNestedRegion region := by
  let A := M.regionSubsystem (M.interior region)
  let AB := M.regionSubsystem region
  let ABC := M.regionSubsystem (region ∪ M.externalBoundary region)
  have hAAB : A.selected ⊆ AB.selected := by
    intro site hsite
    exact (Finset.mem_sdiff.mp hsite).1
  have hABABC : AB.selected ⊆ ABC.selected := by
    intro site hsite
    exact Finset.mem_union_left _ hsite
  let splitAB : Semantics.UnitaryTransport AB.selectedSystem
      (Semantics.CompositeSystem A.selectedSystem (A.additionalRetainedSystem AB)) := by
    let e := A.selectedFactorization AB hAAB
    exact
      { toLinearEquiv := e.toLinearEquiv
        map_inner := e.map_inner }
  have hNested :
      nestedFactorizationLeft AB ABC hABABC =
        nestedFactorizationRight AB ABC hABABC := by
    apply unitaryTransport_ext
    exact nestedFactorization_toLinearEquiv_eq AB ABC hABABC
  change composeUnitaryTransport
      (composeUnitaryTransport (nestedFactorizationLeft AB ABC hABABC)
        (unitaryRTensor splitAB
          (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)))
      (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)) =
    composeUnitaryTransport
      (composeUnitaryTransport (nestedFactorizationRight AB ABC hABABC)
        (unitaryRTensor splitAB
          (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)))
      (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem))
  exact congrArg (fun transport => composeUnitaryTransport
    (composeUnitaryTransport transport
      (unitaryRTensor splitAB
        (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem)))
    (tensorAssociatorUnitary A.selectedSystem (A.additionalRetainedSystem AB)
      (Semantics.CompositeSystem (AB.additionalRetainedSystem ABC) ABC.complementSystem))) hNested
end QEC.Bounds.BPTCommutingProjectorModel
