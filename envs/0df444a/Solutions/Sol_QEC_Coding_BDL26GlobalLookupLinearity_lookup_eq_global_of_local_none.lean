-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.lookup_eq_global_of_local_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:42:27.049828+00:00
-- url     : https://prove2.me/submissions/b3066928-3a25-4602-bed9-e2889ab7ebbc

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
    (isLocal : Word Bit A → Bool) (s : Word Bit B)
    (h : search (fun e => isLocal e && decide (L e=s)) (allWords A)=none) :
    lookup (allWords A) L isLocal 0 s=G L s := by
  unfold lookup
  rw [h]
  rfl
end QEC.Coding.BDL26GlobalLookupLinearity
