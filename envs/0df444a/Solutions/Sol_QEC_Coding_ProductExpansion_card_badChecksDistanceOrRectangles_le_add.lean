-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badChecksDistanceOrRectangles_le_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:05:51.129187+00:00
-- url     : https://prove2.me/submissions/65099d47-5c73-45ff-b326-88f58175fa71

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_badChecksDistanceOrRectanglesEncoding_injective

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (d s m k : Nat) :
    Nat.card (badChecksDistanceOrRectangles (R := R) h' d s m k) ≤
      Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) +
        Nat.card (badChecksAllExactRectangles (R := R) h' s m k) := by
  classical
  calc
    Nat.card (badChecksDistanceOrRectangles (R := R) h' d s m k) ≤
        Nat.card
          (badChecksForDistance (F := F) (W := W) (R := R) d ⊕
            badChecksAllExactRectangles (R := R) h' s m k) :=
      Nat.card_le_card_of_injective
        (badChecksDistanceOrRectanglesEncoding (R := R) h' d s m k)
        (badChecksDistanceOrRectanglesEncoding_injective
          (R := R) h' d s m k)
    _ = Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) +
        Nat.card (badChecksAllExactRectangles (R := R) h' s m k) := by
      rw [Nat.card_sum]
end QEC.Coding.ProductExpansion
