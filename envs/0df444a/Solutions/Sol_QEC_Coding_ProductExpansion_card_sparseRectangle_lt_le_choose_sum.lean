-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_sparseRectangle_lt_le_choose_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:03:38.418823+00:00
-- url     : https://prove2.me/submissions/e3e0f6c1-3142-4dcd-a411-c25337429f8d

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_sparseRectangle_lt_le_support_sum
import Theorems.Thm_QEC_Coding_ProductExpansion_sparseRectangle_support_sum_eq_choose_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    [DecidableEq W] (A B : Finset W) (s : Nat) :
    Nat.card {x : Matrix W W F // restrictedWeight x A B < s} ≤
      ∑ t : Fin s, Nat.choose (A.card * B.card) t.1 *
        (Nat.card F) ^
          ((Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + t.1) := by
  exact (card_sparseRectangle_lt_le_support_sum (F := F) A B s).trans_eq
    (sparseRectangle_support_sum_eq_choose_sum (F := F) A B s)
end QEC.Coding.ProductExpansion
