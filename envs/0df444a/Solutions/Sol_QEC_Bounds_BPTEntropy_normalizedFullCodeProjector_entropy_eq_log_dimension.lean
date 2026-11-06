-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.normalizedFullCodeProjector_entropy_eq_log_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:09:31.731832+00:00
-- url     : https://prove2.me/submissions/1140efc0-d7d1-437c-bb7d-76624c76a8d4

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedCodeProjector_entropy_eq_log_dimension

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
      Real.logb 2 (M.codeSpace.dimension : Real) := by
  unfold normalizedFullCodeProjector
  exact normalizedCodeProjector_entropy_eq_log_dimension M.codeSpace
    (bptCodeDimension_pos M parameter)
end QEC.Bounds.BPTEntropy
