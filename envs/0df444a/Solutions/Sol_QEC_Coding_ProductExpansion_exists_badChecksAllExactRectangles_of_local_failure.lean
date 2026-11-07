-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_badChecksAllExactRectangles_of_local_failure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:19:57.053202+00:00
-- url     : https://prove2.me/submissions/a62ba03b-78e2-454f-9b93-14046e31db02

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_restrictedWeight_mono
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_local_syndrome_rank_weight_inequality_five_thirtysixths
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F) (d m s k : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hRankTarget : 36 * k * s ≤ 5 * d * d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A B : Finset W)
    (hLargeA : Fintype.card W - m ≤ A.card)
    (hLargeB : Fintype.card W - m ≤ B.card)
    (hWeight : restrictedWeight x A B < s) :
    ∃ bad : badChecksAllExactRectangles (R := R) h' s m k, bad.1 = h := by
  classical
  obtain ⟨A₀, hA₀A, hA₀Card⟩ :=
    Finset.exists_subset_card_eq hLargeA
  obtain ⟨B₀, hB₀B, hB₀Card⟩ :=
    Finset.exists_subset_card_eq hLargeB
  have hWeight₀ : restrictedWeight x A₀ B₀ < s :=
    (restrictedWeight_mono x hA₀A hB₀B).trans_lt hWeight
  have hRank := local_syndrome_rank_weight_inequality_five_thirtysixths
    h h' d m hPositive hLength hSmallM hDistance hDistance'
      x hx hxNonzero hMinimal A₀ B₀
      (by rw [hA₀Card]) (by rw [hB₀Card])
  have hsPositive : 0 < s := lt_of_le_of_lt (Nat.zero_le _) hWeight₀
  have hChain : 36 * k * s ≤ 36 * (h' * x).rank * s := by
    calc
      36 * k * s ≤ 5 * d * d := hRankTarget
      _ ≤ 36 * (h' * x).rank * restrictedWeight x A₀ B₀ := hRank
      _ ≤ 36 * (h' * x).rank * s :=
        Nat.mul_le_mul_left (36 * (h' * x).rank) (Nat.le_of_lt hWeight₀)
  have hKs : k * s ≤ (h' * x).rank * s := by
    apply (Nat.mul_le_mul_left_iff (by omega : 0 < 36)).mp
    simpa [mul_assoc] using hChain
  have hk : k ≤ (h' * x).rank :=
    Nat.le_of_mul_le_mul_right hKs hsPositive
  refine ⟨⟨h, ?_⟩, rfl⟩
  exact ⟨A₀, B₀, hA₀Card, hB₀Card, x, hWeight₀, hk, hx⟩
end QEC.Coding.ProductExpansion
