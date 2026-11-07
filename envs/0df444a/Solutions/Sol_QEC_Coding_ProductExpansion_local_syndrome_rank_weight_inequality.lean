-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.local_syndrome_rank_weight_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:16:37.053876+00:00
-- url     : https://prove2.me/submissions/86cc3c90-9c19-483e-b7c0-17c7155945ac

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_card_columnsOutside_lightGenerators_ge_distance
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_min_weight_syndrome_generators
import Theorems.Thm_QEC_Coding_ProductExpansion_rectangle_weight_ge_escaping_columns
import Theorems.Thm_QEC_Coding_ProductExpansion_card_inter_ge_distance_sub_missing

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A B : Finset W)
    (hLargeA : Fintype.card W - m ≤ A.card)
    (hLargeB : Fintype.card W - m ≤ B.card) :
    d * (d - m) ≤ 6 * (h' * x).rank * restrictedWeight x A B := by
  classical
  obtain ⟨C, hCard, hSpanning, hMin⟩ :=
    exists_min_weight_syndrome_generators h' x A
  let E := columnsOutsideSyndromeSpan h' x (lightGenerators A C d)
  have hOutside : d ≤ E.card := card_columnsOutside_lightGenerators_ge_distance
    h h' d m hPositive hLength hSmallM hDistance hDistance'
    x hx hxNonzero hMinimal A hLargeA C hCard
  have hIntersection : d - m ≤ (E ∩ B).card :=
    card_inter_ge_distance_sub_missing E B d m hOutside hLargeB
  have hRectangle := rectangle_weight_ge_escaping_columns
    h' x A B d C hCard hSpanning hMin
  have hLower := Nat.mul_le_mul_left d hIntersection
  change d * (d - m) ≤ d * (E ∩ B).card at hLower
  change d * (E ∩ B).card ≤ 6 * C.card * restrictedWeight x A B at hRectangle
  rw [hCard] at hRectangle
  exact hLower.trans hRectangle
end QEC.Coding.ProductExpansion
