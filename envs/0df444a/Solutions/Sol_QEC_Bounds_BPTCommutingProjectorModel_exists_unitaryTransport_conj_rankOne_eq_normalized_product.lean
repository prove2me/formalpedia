-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.exists_unitaryTransport_conj_rankOne_eq_normalized_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:41:45.624523+00:00
-- url     : https://prove2.me/submissions/47e71839-495c-42b5-a694-652f7434b258

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductUnitary
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_unitaryTransport_map_eq_normalized_product
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne


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
    {N C : Type u} [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] (psi : Semantics.CompositeSystem N C) (hpsi : ‖psi‖ = 1) :
    ∃ n0 : N, ∃ c0 : C, ‖n0‖ = 1 ∧ ‖c0‖ = 1 ∧
      ∃ U : Semantics.UnitaryTransport (Semantics.CompositeSystem N C)
        (Semantics.CompositeSystem N C), U psi = n0 ⊗ₜ[Complex] c0 ∧
        U.conjOperator (InnerProductSpace.rankOne Complex psi psi).toLinearMap =
          (InnerProductSpace.rankOne Complex (n0 ⊗ₜ[Complex] c0)
            (n0 ⊗ₜ[Complex] c0)).toLinearMap := by
  rcases exists_unitaryTransport_map_eq_normalized_product psi hpsi with
    ⟨n0, c0, hn0, hc0, U, hU⟩
  refine ⟨n0, c0, hn0, hc0, U, hU, ?_⟩
  rw [Semantics.QuditSubsystem.conjOperator_rankOne, hU]
end QEC.Bounds.BPTCommutingProjectorModel
