-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.bpt_correctable_region_entropy_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:33:56.804118+00:00
-- url     : https://prove2.me/submissions/4ad5dbe5-95b5-4305-8e6e-f8a97178a97c

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_erasure_correctable_entropy_identity

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u
namespace QEC.Bounds.BPTEntropy
theorem _root_.solution
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ) (region : Finset L.Site)
    (recovery : QuantumChannel (M.regionSubsystem region).complementSystem L.Register)
    (hcorrect : Correctable L.Register (M.regionSubsystem region).complementSystem M.codeSpace
      (M.regionSubsystem region).erasureChannelFromRegister recovery)
    (rho : DensityOperator L.Register)
    (hsupported : DensityOperator.SupportedOn M.codeSpace rho) :
    rho.vonNeumannEntropy -
        ((M.regionSubsystem region).erasureChannelFromRegister.mapDensity rho).vonNeumannEntropy =
      - ((M.regionSubsystem region).selectedPartialTraceFromRegister.mapDensity rho).vonNeumannEntropy := by
  exact erasure_correctable_entropy_identity (M.regionSubsystem region) M.codeSpace recovery
    hcorrect rho hsupported
end QEC.Bounds.BPTEntropy
