-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.normalizedFullCodeProjector_supportedOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:33:59.874143+00:00
-- url     : https://prove2.me/submissions/de822596-be46-4917-9e70-e2a1ece73051

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedCodeProjector_supportedOn

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
    DensityOperator.SupportedOn M.codeSpace (normalizedFullCodeProjector M parameter) := by
  unfold normalizedFullCodeProjector
  exact normalizedCodeProjector_supportedOn M.codeSpace (bptCodeDimension_pos M parameter)
end QEC.Bounds.BPTEntropy
