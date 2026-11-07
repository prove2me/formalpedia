-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.distance_le_four_mul_restrictedHammingWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:05:21.005318+00:00
-- url     : https://prove2.me/submissions/84d3506c-f64a-4122-bce4-33b3f1973602

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_le_restrictedHammingWeight_add_complement

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (A : Finset W) (x : Word F W) (d m : Nat)
    (hA : Fintype.card W - m ≤ A.card)
    (hHeavy : d ≤ 2 * HammingWeight x)
    (hDistance : 4 * m ≤ d) :
    d ≤ 4 * restrictedHammingWeight A x := by
  have hMissing : Fintype.card W - A.card ≤ m := by
    have hAUniv : A.card ≤ Fintype.card W := Finset.card_le_univ A
    omega
  have hTotal := HammingWeight_le_restrictedHammingWeight_add_complement A x
  omega
end QEC.Coding.ProductExpansion
