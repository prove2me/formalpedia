-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.projectorBC_mul_CD_supportedOnRegister
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:09:04.330363+00:00
-- url     : https://prove2.me/submissions/93958e54-5963-4b37-96d5-efa231e886a1

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
    (M.regionSubsystem (M.boundary region ∪ regionᶜ)).OperatorSupportedOnRegister
      (M.projectorBC region * M.projectorCD region) := by
  have h1 := operatorSupportedOnRegister_of_subset (M.regionSubsystem (M.boundary region))
    (M.regionSubsystem (M.boundary region ∪ regionᶜ))
    (fun x hx => Finset.mem_union_left _ hx) (M.projectorBC_supportedOnRegister_boundary region)
  have h2 := operatorSupportedOnRegister_of_subset (M.regionSubsystem regionᶜ)
    (M.regionSubsystem (M.boundary region ∪ regionᶜ))
    (fun x hx => Finset.mem_union_right _ hx) (M.projectorCD_supportedOnRegister_complement region)
  exact M.operatorSupportedOnRegister_comp (M.boundary region ∪ regionᶜ) h1 h2
