-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection.input_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:10:09.061189+00:00
-- url     : https://prove2.me/submissions/3ef28b37-8e2b-4a2f-817e-95e208247e2c

import Definitions.Def_QEC_Coding_BitTuring_UnaryOutputEquality
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FieldProjection_stream_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
open Turing StateTransition
variable (n:ℕ) (keep:Fin (n+1) → Bool)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
theorem _root_.solution : Function.Injective (input n) := by
  intro x y h;exact Subtype.ext (stream_injective h)
end QEC.Coding.BitTuring.UnaryArithmetic.FieldProjection
