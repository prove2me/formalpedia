-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFree6812.derivation_order_of_basis_yukon_abb914525d86
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T17:58:20.884263+00:00
-- url     : https://prove2.me/submissions/a6719ece-8407-45f6-b5cd-e226e7a8fa43

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
section Bridges
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : Valuation L ℤᵐ⁰) (D : Derivation K L L)
/-- (i) in the form of the task statement: `t i ∈ O_v` with `pole (D (t i)) ≤ s`, the
residue field separable over `K(t̄)`, crude continuity, `s ≤ θ` and `1 - ord (Dπ) ≤ θ`. -/
theorem _root_.solution [v.IsTrivialOn K] {ι : Type*} (t : ι → L)
    (π : L) (hπ : v π = exp (-1)) (s θ : ℤ) (hs : 0 ≤ s) (hsθ : s ≤ θ)
    (hπθ : v (D π) ≤ exp (θ - 1)) (ht : ∀ i, v (t i) ≤ 1) (hDt : ∀ i, v (D (t i)) ≤ exp s)
    (C : ℤ) (hcont : CrudeBound v D C)
    [Algebra.IsSeparable (Subfield.closure (residue v '' (Set.range (algebraMap K L) ∪
      Set.range t))) (IsLocalRing.ResidueField v.valuationSubring)] (f : L) :
    v (D f) ≤ exp θ * v f  := derivation_order v D π hπ s θ hs hsθ hπθ C hcont
    (residuallySeparable_of_isSeparable v D (exp s) _ (tame_constants_and_basis v D t s ht hDt))
    f
end Bridges
end HFree6812
end SubmissionLower
end ProximityPrize
