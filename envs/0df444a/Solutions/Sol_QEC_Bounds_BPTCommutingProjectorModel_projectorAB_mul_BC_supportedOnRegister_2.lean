-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.projectorAB_mul_BC_supportedOnRegister
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:09:03.500242+00:00
-- url     : https://prove2.me/submissions/9a1525a4-0afe-4a42-959e-d55b098c455a

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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.regionSubsystem (region ∪ M.boundary region)).OperatorSupportedOnRegister
      (M.projectorAB region * M.projectorBC region) := by
  have h1 := operatorSupportedOnRegister_of_subset (M.regionSubsystem region)
    (M.regionSubsystem (region ∪ M.boundary region))
    (fun x hx => Finset.mem_union_left _ hx) (M.projectorAB_supportedOnRegister_region region)
  have h2 := operatorSupportedOnRegister_of_subset (M.regionSubsystem (M.boundary region))
    (M.regionSubsystem (region ∪ M.boundary region))
    (fun x hx => Finset.mem_union_right _ hx) (M.projectorBC_supportedOnRegister_boundary region)
  exact M.operatorSupportedOnRegister_comp (region ∪ M.boundary region) h1 h2
