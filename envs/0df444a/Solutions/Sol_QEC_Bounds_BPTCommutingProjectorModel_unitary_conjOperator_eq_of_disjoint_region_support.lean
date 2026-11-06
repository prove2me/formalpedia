-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.unitary_conjOperator_eq_of_disjoint_region_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:26:50.759818+00:00
-- url     : https://prove2.me/submissions/0389a30b-8da9-4c8c-97bc-6b66a91cb71b

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commute_of_disjoint_region_support
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_conjOperator_eq_of_intertwines


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
    (hB : (M.regionSubsystem operatorRegion).OperatorSupportedOnRegister B) :
    U.conjOperator B = B := by
  apply unitaryTransport_conjOperator_eq_of_intertwines U B B
  exact (M.commute_of_disjoint_region_support unitaryRegion operatorRegion hdisjoint hU hB).eq
end QEC.Bounds.BPTCommutingProjectorModel
