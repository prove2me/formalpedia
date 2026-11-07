-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.column_vanish_outside_generatorSupport_of_small_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:03:18.388457+00:00
-- url     : https://prove2.me/submissions/802840e7-ab19-4e2b-810c-0e9cf17f853b

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_column_eq_small_support_syndrome_lift
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_supported_syndrome_lift_of_mem_span
import Theorems.Thm_QEC_Coding_ProductExpansion_generatorSupport_card_lt_one_third_of_small_restricted_weight

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hLength : d ≤ Fintype.card W) (hSmallM : 6 * m ≤ d)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W))
    (hWeight : (generatorRestrictedWeight A C : ℝ) < (d : ℝ) / 6)
    (j : W) (hSyndrome : h'.mulVec (column x j) ∈ syndromeSpan h' C) :
    ∀ i ∉ generatorSupport C, x i j = 0 := by
  have hSmallSupport :=
    generatorSupport_card_lt_one_third_of_small_restricted_weight
      d m hLength hSmallM A hLargeA C hWeight
  obtain ⟨y, hSupported, hLift⟩ :=
    exists_supported_syndrome_lift_of_mem_span
      h' C (h'.mulVec (column x j)) hSyndrome
  have hEqual := column_eq_small_support_syndrome_lift
    h h' d hDistance' x hMinimal (generatorSupport C)
      hSmallSupport j y hSupported hLift
  intro i hi
  exact (congrFun hEqual i).trans (hSupported i hi)
end QEC.Coding.ProductExpansion
