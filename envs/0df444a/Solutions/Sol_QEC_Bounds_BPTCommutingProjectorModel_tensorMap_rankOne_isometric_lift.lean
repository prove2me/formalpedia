-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.tensorMap_rankOne_isometric_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-18T04:14:11.80449+00:00
-- url     : https://prove2.me/submissions/a5b0c886-e946-4b35-8dc8-53027d1dbd67

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isometric_lift_rankOne_self


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
    {S T H K : Type u}
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    [NormedAddCommGroup T] [InnerProductSpace Complex T] [Semantics.FiniteQuantumSystem T]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (eSel : S →ₗ[Complex] H) (heSel : (LinearMap.adjoint eSel).comp eSel =
      (1 : Semantics.Operator S))
    (eComp : T →ₗ[Complex] K) (phi : S) (P : Semantics.Operator T) :
    TensorProduct.map (InnerProductSpace.rankOne Complex (eSel phi) (eSel phi)).toLinearMap
        (eComp.comp (P.comp (LinearMap.adjoint eComp))) =
      (TensorProduct.map eSel eComp).comp
        ((TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap P).comp
          (LinearMap.adjoint (TensorProduct.map eSel eComp))) := by
  rw [← isometric_lift_rankOne_self eSel heSel phi]
  rw [TensorProduct.adjoint_map, ← TensorProduct.map_comp, ← TensorProduct.map_comp]
end QEC.Bounds.BPTCommutingProjectorModel
