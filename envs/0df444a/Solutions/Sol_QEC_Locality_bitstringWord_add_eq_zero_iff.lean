-- Prove2me | solution 1 for QEC.Locality.bitstringWord_add_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:48:58.303666+00:00
-- url     : https://prove2.me/submissions/7a3f5d82-2aaa-40da-93a9-375c3f956ea5

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_word_add_self_zero
import Theorems.Thm_QEC_Locality_word_neg_eq_self

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {α : Type u} [Fintype α] [DecidableEq α]
    (a b : Qubit.Bitstring α) :
    PauliSymplectic.bitstringWordEquiv α b +
        PauliSymplectic.bitstringWordEquiv α a = 0 ↔ b = a := by
  constructor
  · intro h
    apply (PauliSymplectic.bitstringWordEquiv α).injective
    rw [eq_neg_of_add_eq_zero_left h, word_neg_eq_self]
  · intro h
    subst b
    exact word_add_self_zero _
end QEC.Locality
