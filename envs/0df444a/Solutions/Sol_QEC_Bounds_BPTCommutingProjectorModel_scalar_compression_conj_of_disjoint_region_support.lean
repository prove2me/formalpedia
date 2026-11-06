-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.scalar_compression_conj_of_disjoint_region_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:07:09.620932+00:00
-- url     : https://prove2.me/submissions/66f8bd3b-12b9-4571-ae6c-70442eda2e97

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitary_conjOperator_eq_of_disjoint_region_support

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (unitaryRegion operatorRegion : Finset L.Site)
    (hdisjoint : Disjoint unitaryRegion operatorRegion)
    (U : Semantics.UnitaryTransport L.Register L.Register)
    (hU : M.UnitarySupportedOn unitaryRegion U)
    {B : Semantics.Operator L.Register}
    (hB : (M.regionSubsystem operatorRegion).OperatorSupportedOnRegister B)
    {scalar : Complex}
    (hscalar : M.fullCodeProjector * B * M.fullCodeProjector =
      scalar • M.fullCodeProjector) :
    U.conjOperator M.fullCodeProjector * B * U.conjOperator M.fullCodeProjector =
      scalar • U.conjOperator M.fullCodeProjector := by
  have hfixed : U.conjOperator B = B :=
    M.unitary_conjOperator_eq_of_disjoint_region_support
      unitaryRegion operatorRegion hdisjoint U hU hB
  calc
    U.conjOperator M.fullCodeProjector * B * U.conjOperator M.fullCodeProjector =
        U.conjOperator M.fullCodeProjector * U.conjOperator B *
          U.conjOperator M.fullCodeProjector := by rw [hfixed]
    _ = U.conjOperator (M.fullCodeProjector * B * M.fullCodeProjector) := by
      rw [Semantics.UnitaryTransport.conjOperator_mul,
        Semantics.UnitaryTransport.conjOperator_mul]
    _ = U.conjOperator (scalar • M.fullCodeProjector) :=
      congrArg U.conjOperator hscalar
    _ = scalar • U.conjOperator M.fullCodeProjector := by
      exact U.conjOperatorLinearMap.map_smul scalar M.fullCodeProjector
end QEC.Bounds.BPTCommutingProjectorModel
