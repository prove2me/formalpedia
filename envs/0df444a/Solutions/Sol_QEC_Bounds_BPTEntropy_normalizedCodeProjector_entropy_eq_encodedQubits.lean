-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.normalizedCodeProjector_entropy_eq_encodedQubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:38:57.724249+00:00
-- url     : https://prove2.me/submissions/ea089b89-5e5a-4d0a-9c16-c59b4de08f39

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
    (normalizedCodeProjector M.codeSpace (by
      rw [parameter.codeDimension_eq_two_pow]
      exact pow_pos (by omega) _)).vonNeumannEntropy =
      (parameter.encodedQubits : Real) := by
  rw [normalizedCodeProjector_entropy_eq_log_dimension]
  rw [parameter.codeDimension_eq_two_pow]
  rw [Nat.cast_pow]
  change Real.logb 2 ((2 : Real) ^ parameter.encodedQubits) = _
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
end QEC.Bounds.BPTEntropy
