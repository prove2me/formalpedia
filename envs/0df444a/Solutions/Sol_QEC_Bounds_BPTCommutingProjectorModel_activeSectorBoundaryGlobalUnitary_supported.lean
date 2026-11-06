-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.activeSectorBoundaryGlobalUnitary_supported
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:02:52.202199+00:00
-- url     : https://prove2.me/submissions/440b409e-cf2a-4504-96ab-e3e20ca62032

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_boundaryLocalUnitaryToRegister_supported

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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {WB NB WC NC : Type} [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC]
    (SB : Submodule Complex (M.fourFactorB region))
    (SC : Submodule Complex (M.fourFactorC region))
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) :
    M.UnitarySupportedOn (M.boundary region)
      (M.activeSectorBoundaryGlobalUnitary region SB SC UB UC U) := by
  unfold activeSectorBoundaryGlobalUnitary
  exact M.boundaryLocalUnitaryToRegister_supported region
    (M.activeSectorBoundaryUnitary region SB SC UB UC U)
end QEC.Bounds.BPTCommutingProjectorModel
