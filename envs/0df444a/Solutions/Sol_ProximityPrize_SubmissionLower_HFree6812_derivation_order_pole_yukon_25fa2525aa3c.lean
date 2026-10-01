-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFree6812.derivation_order_pole_yukon_25fa2525aa3c
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T17:58:23.765552+00:00
-- url     : https://prove2.me/submissions/db543ed8-0373-4d24-aba3-229138d176bd

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
/-- (i) Pole form: `pole (D f) ≤ pole f + θ`. -/
theorem _root_.solution (π : L) (hπ : v π = exp (-1)) (s θ : ℤ) (hs : 0 ≤ s)
    (hsθ : s ≤ θ) (hπθ : v (D π) ≤ exp (θ - 1)) (C : ℤ)
    (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D (exp s)) (f : L) :
    max 0 (v (D f)).log ≤ max 0 (v f).log + θ  := pole_le_of_le v θ (by omega) f (D f)
    (derivation_order v D π hπ s θ hs hsθ hπθ C hcont hsep f)
end Core
end HFree6812
end SubmissionLower
end ProximityPrize
