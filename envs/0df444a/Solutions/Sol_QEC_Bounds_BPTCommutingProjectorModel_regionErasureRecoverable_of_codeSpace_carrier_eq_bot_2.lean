-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_of_codeSpace_carrier_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:08:59.832512+00:00
-- url     : https://prove2.me/submissions/a20b12d3-7b14-47c8-ad9e-9182bff51690

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Support
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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcode : M.codeSpace.carrier = ⊥) :
    M.RegionErasureRecoverable region := by
  refine ⟨(M.regionSubsystem region).prepareSelected
    ((M.regionSubsystem region).maximallyMixedSelected L.localDimension_positive), ?_⟩
  intro rho hrho
  exfalso
  have h0 : rho.toOperator = 0 := by
    apply LinearMap.ext
    intro v
    have hv := hrho v
    rw [hcode] at hv
    simpa using hv
  have h1 := rho.trace_one
  rw [h0] at h1
  simp at h1
