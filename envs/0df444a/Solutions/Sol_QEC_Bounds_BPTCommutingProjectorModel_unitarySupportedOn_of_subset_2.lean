-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.unitarySupportedOn_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:09:02.624624+00:00
-- url     : https://prove2.me/submissions/9c505660-7466-4c44-918f-3121223a1866

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (S T : Finset L.Site)
    {U : Semantics.UnitaryTransport L.Register L.Register}
    (hST : S ⊆ T) (hU : M.UnitarySupportedOn S U) :
    M.UnitarySupportedOn T U := by
  exact operatorSupportedOnRegister_of_subset (M.regionSubsystem S) (M.regionSubsystem T)
    (fun x hx => hST hx) hU
