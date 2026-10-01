-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFree6812.derivation_order_iterate_pole_yukon_9a1a3b6a87f3
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T18:04:04.079611+00:00
-- url     : https://prove2.me/submissions/5326ccb3-5b18-4012-b4ad-a688c43a011b

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Separable


import Init
import Theorems.Thm_ProximityPrize_SubmissionLower_HFree6812_derivation_order_iterate_yukon_37deb23af724
import Definitions.Def_Yukon_a9a7f17ede75ca0ceb0597e1
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.HFree6812.derivation_order_iterate := @ProximityPrize.SubmissionLower.HFree6812.derivation_order_iterate_yukon_37deb23af724
namespace Polynomial
end Polynomial
namespace WithZero
end WithZero
namespace ProximityPrize.SubmissionLower.HFree6812
open WithZero Polynomial
section Core
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : Valuation L ℤᵐ⁰) (D : Derivation K L L)
/-- Iterated pole form: `pole (Dᵏ f) ≤ pole f + k θ`. -/
theorem _root_.solution (π : L) (hπ : v π = exp (-1)) (s θ : ℤ) (hs : 0 ≤ s)
    (hsθ : s ≤ θ) (hπθ : v (D π) ≤ exp (θ - 1)) (C : ℤ)
    (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D (exp s)) (k : ℕ) (f : L) :
    max 0 (v ((⇑D)^[k] f)).log ≤ max 0 (v f).log + k * θ  := pole_le_of_le v (k * θ) (mul_nonneg (by positivity) (by omega)) f _
    (derivation_order_iterate v D π hπ s θ hs hsθ hπθ C hcont hsep k f)
end Core
end HFree6812
end SubmissionLower
end ProximityPrize
