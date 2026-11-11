-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.residual_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:41:59.90274+00:00
-- url     : https://prove2.me/submissions/9b9cb822-3919-460d-a750-4b8900d8acd6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]
namespace QEC.Coding.BDL26GlobalLookupLinearity
theorem _root_.solution (L : Word Bit A →ₗ[Bit] Word Bit B)
    (a : Word Bit A) : L (a+G L (L a))=0 := by
  rw [map_add,global_preimage L (L a) ⟨a,rfl⟩]
  exact word_add_self (L a)
end QEC.Coding.BDL26GlobalLookupLinearity
