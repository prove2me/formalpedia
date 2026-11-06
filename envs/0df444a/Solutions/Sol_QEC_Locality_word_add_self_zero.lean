-- Prove2me | solution 1 for QEC.Locality.word_add_self_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:37:48.582202+00:00
-- url     : https://prove2.me/submissions/1917065d-25e5-4fe8-9e7b-295d2207110d

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer

set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution {α : Type u} [Fintype α]
    (x : Coding.Word (ZMod 2) α) : x + x = 0 := by
  ext i
  rw [← two_mul]
  have htwo : (2 : ZMod 2) = 0 := by decide
  change (2 : ZMod 2) * x i = 0
  rw [htwo, zero_mul]
end QEC.Locality
