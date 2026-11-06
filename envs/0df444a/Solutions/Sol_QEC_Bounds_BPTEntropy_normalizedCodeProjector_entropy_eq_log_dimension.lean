-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.normalizedCodeProjector_entropy_eq_log_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:36:19.875977+00:00
-- url     : https://prove2.me/submissions/65b07265-cad6-4cc9-b5dc-059ccfbd9b97

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_vonNeumannEntropy_eq_log_finrank_of_uniform_id
import Theorems.Thm_QEC_Bounds_BPTEntropy_rightMarginal_codeCarrierPurification_eq_normalizedCodeProjector
import Theorems.Thm_QEC_Bounds_BPTEntropy_leftMarginal_codeCarrierPurification_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure


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
theorem _root_.solution {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    (normalizedCodeProjector C hdim).vonNeumannEntropy =
      Real.logb 2 (C.dimension : Real) := by
  let psi := codeCarrierPurificationVector C
  let hpsi : ‖psi‖ ^ 2 = 1 := codeCarrierPurificationVector_normSq C hdim
  have hright := rightMarginal_codeCarrierPurification_eq_normalizedCodeProjector C hdim
  have hpure := vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure psi hpsi
  have huniform := vonNeumannEntropy_eq_log_finrank_of_uniform_id
    (leftMarginal (pureDensity psi hpsi)) (leftMarginal_codeCarrierPurification_toOperator C hdim)
  calc
    (normalizedCodeProjector C hdim).vonNeumannEntropy =
        (rightMarginal (pureDensity psi hpsi)).vonNeumannEntropy := by
          rw [hright]
    _ = (leftMarginal (pureDensity psi hpsi)).vonNeumannEntropy := hpure
    _ = Real.logb 2 (Module.finrank Complex C.carrier : Real) := huniform
    _ = Real.logb 2 (C.dimension : Real) := rfl
end QEC.Bounds.BPTEntropy
