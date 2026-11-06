-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.normalizedCodeProjector_supportedOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:10:59.655982+00:00
-- url     : https://prove2.me/submissions/347bc7c7-07ba-4588-a587-44fc8d0014c3

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedCodeProjector_toOperator
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_mem_carrier


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
    DensityOperator.SupportedOn C (normalizedCodeProjector C hdim) := by
  intro vector
  rw [normalizedCodeProjector_toOperator]
  exact C.carrier.smul_mem _ (C.projector_mem_carrier vector)
end QEC.Bounds.BPTEntropy
