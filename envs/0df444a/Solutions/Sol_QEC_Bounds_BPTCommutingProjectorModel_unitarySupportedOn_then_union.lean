-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.unitarySupportedOn_then_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:04:32.865553+00:00
-- url     : https://prove2.me/submissions/a75f4ab7-b0db-42a3-8f58-3c706751325d

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_operatorSupportedOnRegister_mul_union

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
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site)
    {U V : Semantics.UnitaryTransport L.Register L.Register}
    (hU : M.UnitarySupportedOn left U) (hV : M.UnitarySupportedOn right V) :
    M.UnitarySupportedOn (left ∪ right) (thenUnitary U V) := by
  have h := M.operatorSupportedOnRegister_mul_union right left hV hU
  rw [Finset.union_comm] at h
  exact h
end QEC.Bounds.BPTCommutingProjectorModel
