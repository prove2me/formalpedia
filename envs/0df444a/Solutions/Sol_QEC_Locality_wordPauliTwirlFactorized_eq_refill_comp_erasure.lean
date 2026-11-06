-- Prove2me | solution 1 for QEC.Locality.wordPauliTwirlFactorized_eq_refill_comp_erasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:58:06.418699+00:00
-- url     : https://prove2.me/submissions/037a4265-4e50-4eb0-b6c3-43a898a1b8ce

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_factorizedBasis_apply
import Theorems.Thm_QEC_Locality_operator_ext_factorized_basis
import Theorems.Thm_QEC_Locality_wordPauliTwirlFactorized_matrix_element
import Theorems.Thm_QEC_Locality_refill_comp_erasure_matrix_element
import Theorems.Thm_QEC_Locality_quantumChannel_ext

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution (S : FiniteSubsystem ι) :
    wordPauliTwirlFactorized S =
      QuantumChannel.comp (refillFactorized S) S.erasureChannel := by
  apply quantumChannel_ext
  apply LinearMap.ext
  intro A
  apply operator_ext_factorized_basis S
  intro p q
  rw [factorizedBasis_apply, factorizedBasis_apply]
  rw [wordPauliTwirlFactorized_matrix_element,
    refill_comp_erasure_matrix_element]
end QEC.Locality
