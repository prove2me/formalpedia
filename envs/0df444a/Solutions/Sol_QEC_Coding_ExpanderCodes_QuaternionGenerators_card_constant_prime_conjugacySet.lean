-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.card_constant_prime_conjugacySet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:48:59.949299+00:00
-- url     : https://prove2.me/submissions/57b53c08-4c2b-4ec5-8d3f-b6adab1fc30f

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_constantTorus_conjugate_prime_injective
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_card_constantTorus


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K)
    [Fintype F] (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon)
    (hEpsilon : epsilon ≠ 0) (hY : y ≠ 0) (hOne : 1 + y ≠ 0)
    (hTwo : (2 : K) ≠ 0) :
    Nat.card (conjugacySet (constantTorus f epsilon y)
      (projectivePrime (f epsilon) y ((map_ne_zero f).mpr hEpsilon) hY hOne)) =
        Fintype.card F + 1 := by
  unfold conjugacySet
  rw [← Nat.card_congr (Equiv.ofInjective _
    (constantTorus_conjugate_prime_injective f epsilon y hEpsilon hY hOne hTwo))]
  exact card_constantTorus f epsilon y hNonSquare hOne hTwo
end QEC.Coding.ExpanderCodes.QuaternionGenerators
