-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFree6812.derivation_order_iterate_yukon_37deb23af724
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T17:55:50.344992+00:00
-- url     : https://prove2.me/submissions/03fdd8bc-b8f7-4a7a-830c-8f168b01df33

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
/-- (i) Iterated: `ord (Dᵏ f) ≥ ord f - k θ`. -/
theorem _root_.solution (π : L) (hπ : v π = exp (-1)) (s θ : ℤ) (hs : 0 ≤ s)
    (hsθ : s ≤ θ) (hπθ : v (D π) ≤ exp (θ - 1)) (C : ℤ)
    (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D (exp s)) (k : ℕ) (f : L) :
    v ((⇑D)^[k] f) ≤ exp (k * θ) * v f  := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine (derivation_order v D π hπ s θ hs hsθ hπθ C hcont hsep _).trans ?_
    refine (mul_le_mul_right ih _).trans ?_
    rw [← mul_assoc, ← exp_add]; push_cast; ring_nf; exact le_rfl
end Core
end HFree6812
end SubmissionLower
end ProximityPrize
