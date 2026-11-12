-- Prove2me | solution 1 for QEC.Coding.BDL26GlobalLookupLinearity.imageSection_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:42:53.827872+00:00
-- url     : https://prove2.me/submissions/2d99eaff-f010-4f48-8a78-5ef259a448fa

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
    (s : LinearMap.range L) : L (imageSection L s)=s.val :=
  global_preimage L s.val s.property
end QEC.Coding.BDL26GlobalLookupLinearity
