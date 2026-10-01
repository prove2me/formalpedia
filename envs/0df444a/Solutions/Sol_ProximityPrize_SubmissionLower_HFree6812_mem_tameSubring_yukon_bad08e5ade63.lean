-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFree6812.mem_tameSubring_yukon_bad08e5ade63
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T17:58:33.759034+00:00
-- url     : https://prove2.me/submissions/c7e94c36-d2c4-486b-9cc8-6fb2ec4cbffc

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Separable


import Init
import Definitions.Def_Yukon_a9a7f17ede75ca0ceb0597e1
set_option backward.isDefEq.respectTransparency.types false
namespace Polynomial
end Polynomial
namespace WithZero
end WithZero
namespace ProximityPrize.SubmissionLower.HFree6812
open WithZero Polynomial
section Core
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : Valuation L ℤᵐ⁰) (D : Derivation K L L)
theorem _root_.solution (Λ : ℤᵐ⁰) (z : L) : z ∈ tameSubring v D Λ ↔ Tame v D Λ z  := Iff.rfl
end Core
end HFree6812
end SubmissionLower
end ProximityPrize
