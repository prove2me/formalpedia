-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.normalizedFullCodeProjector_entropy_eq_encodedQubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:40:52.648204+00:00
-- url     : https://prove2.me/submissions/f5b5f3e4-5c8e-47bd-8f57-97ab9f51cf09

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedCodeProjector_entropy_eq_encodedQubits

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
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M) :
    (normalizedFullCodeProjector M parameter).vonNeumannEntropy =
      (parameter.encodedQubits : Real) := by
  unfold normalizedFullCodeProjector
  exact normalizedCodeProjector_entropy_eq_encodedQubits M parameter
end QEC.Bounds.BPTEntropy
