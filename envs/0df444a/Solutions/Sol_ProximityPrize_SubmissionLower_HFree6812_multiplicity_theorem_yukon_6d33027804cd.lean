-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.HFree6812.multiplicity_theorem_yukon_6d33027804cd
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-30T18:06:19.28836+00:00
-- url     : https://prove2.me/submissions/3306b6dc-0e07-4c61-a878-7744ae811b65

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.Separable


import Init
import Theorems.Thm_ProximityPrize_SubmissionLower_HFree6812_pi_bound_of_element_yukon_082a13d8a402
import Definitions.Def_Yukon_a9a7f17ede75ca0ceb0597e1
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.HFree6812.pi_bound_of_element := @ProximityPrize.SubmissionLower.HFree6812.pi_bound_of_element_yukon_082a13d8a402
namespace Polynomial
end Polynomial
namespace WithZero
end WithZero
namespace ProximityPrize.SubmissionLower.HFree6812
open WithZero Polynomial
section Core
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (v : Valuation L ℤᵐ⁰) (D : Derivation K L L)
/-- (ii) The local multiplicity theorem: if `R ⊆ O_v`, `D R ⊆ R + R σ` with
`pole σ ≤ T`, `s ≤ T`, and some `f ∈ R` has `ord f = n₁` with `n₁` a unit in `K`, then
`θ := T + n₁` satisfies the derivation-order lemma. -/
theorem _root_.solution [v.IsTrivialOn K] (π : L) (hπ : v π = exp (-1)) (s : ℤ)
    (hs : 0 ≤ s) (C : ℤ) (hcont : CrudeBound v D C) (hsep : ResiduallySeparable v D (exp s))
    (R : Subring L) (hR : ∀ r ∈ R, v r ≤ 1) (σ : L) (T : ℤ) (hT : 0 ≤ T)
    (hσ : v σ ≤ exp T) (hDR : ∀ r ∈ R, ∃ a ∈ R, ∃ b ∈ R, D r = a + b * σ) (hsT : s ≤ T)
    (f : L) (hfR : f ∈ R) (n : ℕ) (hn : (n : K) ≠ 0) (hf : v f = exp (-(n : ℤ))) :
    v (D π) ≤ exp (T + n - 1) ∧ ∀ g : L, v (D g) ≤ exp (T + n) * v g  := by
  have hDf : v (D f) ≤ exp T := by
    obtain ⟨a, ha, b, hb, hab⟩ := hDR f hfR
    rw [hab]
    refine (v.map_add _ _).trans (max_le ?_ ?_)
    · exact (hR a ha).trans (by rw [← exp_zero, exp_le_exp]; exact hT)
    · rw [v.map_mul]
      exact (mul_le_mul_left (hR b hb) _).trans (by rw [one_mul]; exact hσ)
  have h1 := pi_bound_of_element v D π hπ s T hsT
    (integral_bound v D π hπ s hs C hcont hsep) f n hn hf hDf
  exact ⟨h1, derivation_order v D π hπ s (T + n) hs (by omega) h1 C hcont hsep⟩
end Core
end HFree6812
end SubmissionLower
end ProximityPrize
