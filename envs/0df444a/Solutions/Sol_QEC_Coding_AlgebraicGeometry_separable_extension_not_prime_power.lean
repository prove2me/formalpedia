-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.separable_extension_not_prime_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:47:13.267695+00:00
-- url     : https://prove2.me/submissions/af269f85-ca3c-4131-a10d-c267b4022e3f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussLocalOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeKronecker
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (K E : Type*) [Field K] [Field E] [Algebra K E] [Algebra.IsSeparable K E]
    (p : ℕ) [ExpChar K p] (a : K) (ha : ∀ b : K, b^p ≠ a) (u : E) :
    u^p ≠ algebraMap K E a := by
  intro heq
  have hadj : IntermediateField.adjoin K {u} = ⊥ := by
    rw [IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable' K E u p]
    exact IntermediateField.adjoin_simple_eq_bot_iff.mpr
      (IntermediateField.mem_bot.mpr ⟨a,heq.symm⟩)
  obtain ⟨b,hb⟩ := IntermediateField.mem_bot.mp
    (IntermediateField.adjoin_simple_eq_bot_iff.mp hadj)
  apply ha b
  apply (algebraMap K E).injective
  rw [map_pow,hb]
  exact heq
end QEC.Coding.AlgebraicGeometry
