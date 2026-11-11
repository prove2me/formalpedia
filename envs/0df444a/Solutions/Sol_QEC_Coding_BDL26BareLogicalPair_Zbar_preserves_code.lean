-- Prove2me | solution 1 for QEC.Coding.BDL26BareLogicalPair.Zbar_preserves_code
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:49:03.893953+00:00
-- url     : https://prove2.me/submissions/afec6e3c-9442-4e99-ad7a-35ade6911574

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_LogicalDimension
import Definitions.Def_QEC_Coding_CSS_Distance
import Definitions.Def_QEC_Coding_Stabilizer_DecoderDressedLogical
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_BareLogicalPair
import Theorems.Thm_QEC_Coding_BDL26BareLogicalPair_logicalZ_normalizer
import Theorems.Thm_QEC_Coding_StabilizerCode_toQubitOperator_mem_code_of_inBinaryNormalizer


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26BareLogicalPair
open Classical Semantics PauliSymplectic BDL26FiniteTannerSquare
open BDL26CSSHamiltonian
open scoped BigOperators
variable (S : OddScale) (m : Nat)
namespace QEC.Coding.BDL26BareLogicalPair
theorem _root_.solution (ψ : Qubit.QubitRegister (Physical S m))
    (hψ : ψ ∈ (labelledCode S m).carrier) : Zbar S m ψ ∈ (labelledCode S m).carrier := by
  change hermitianPhaseScalar (logicalZ S m) • (toQubitOperator (logicalZ S m) ψ) ∈ _
  exact (labelledCode S m).carrier.smul_mem _
    (StabilizerCode.toQubitOperator_mem_code_of_inBinaryNormalizer
      (sourceValid S m) (logicalZ_normalizer S m) hψ)
end QEC.Coding.BDL26BareLogicalPair
