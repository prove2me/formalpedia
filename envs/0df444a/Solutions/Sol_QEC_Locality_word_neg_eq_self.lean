-- Prove2me | solution 1 for QEC.Locality.word_neg_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:46:50.425449+00:00
-- url     : https://prove2.me/submissions/270f2e17-329b-4914-8305-b4ecf87e5892

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
import Theorems.Thm_QEC_Locality_word_add_self_zero

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {α : Type u} [Fintype α]
    (x : Coding.Word (ZMod 2) α) : -x = x := by
  exact (eq_neg_of_add_eq_zero_left (word_add_self_zero x)).symm
end QEC.Locality
