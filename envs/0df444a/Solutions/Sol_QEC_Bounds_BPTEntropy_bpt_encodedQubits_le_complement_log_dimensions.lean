-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.bpt_encodedQubits_le_complement_log_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:09:34.121387+00:00
-- url     : https://prove2.me/submissions/7cc07480-53b0-46f7-abf7-1f509c80973c

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedFullCodeProjector_entropy_eq_encodedQubits
import Theorems.Thm_QEC_Bounds_BPTEntropy_bpt_normalizedFullCodeProjector_entropy_le_complement_log_dimensions

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
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (A B : Finset L.Site) (hdisjoint : Disjoint A B)
    (recoveryA : QuantumChannel (M.regionSubsystem A).complementSystem L.Register)
    (hcorrectA : Correctable L.Register (M.regionSubsystem A).complementSystem M.codeSpace
      (M.regionSubsystem A).erasureChannelFromRegister recoveryA)
    (recoveryB : QuantumChannel (M.regionSubsystem B).complementSystem L.Register)
    (hcorrectB : Correctable L.Register (M.regionSubsystem B).complementSystem M.codeSpace
      (M.regionSubsystem B).erasureChannelFromRegister recoveryB) :
    (parameter.encodedQubits : Real) <=
      ∑ i : (_root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem (M.regionSubsystem A)
        (M.regionSubsystem B)).ComplementCoordinates,
        Real.logb 2 (L.localDimension i : Real) := by
  calc
    (parameter.encodedQubits : Real) = (normalizedFullCodeProjector M parameter).vonNeumannEntropy :=
      (normalizedFullCodeProjector_entropy_eq_encodedQubits M parameter).symm
    _ <= ∑ i : (_root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem
        (M.regionSubsystem A) (M.regionSubsystem B)).ComplementCoordinates,
        Real.logb 2 (L.localDimension i : Real) :=
      bpt_normalizedFullCodeProjector_entropy_le_complement_log_dimensions M parameter A B
        hdisjoint recoveryA hcorrectA recoveryB hcorrectB
end QEC.Bounds.BPTEntropy
