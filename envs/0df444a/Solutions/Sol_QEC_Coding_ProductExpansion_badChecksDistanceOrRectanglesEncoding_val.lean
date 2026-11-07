-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.badChecksDistanceOrRectanglesEncoding_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:02:22.298868+00:00
-- url     : https://prove2.me/submissions/c4e5dae3-3d2a-489d-8f32-57499f4e6415

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (d s m k : Nat)
    (h : badChecksDistanceOrRectangles (R := R) h' d s m k) :
    Sum.elim Subtype.val Subtype.val
      (badChecksDistanceOrRectanglesEncoding (R := R) h' d s m k h) = h.1 := by
  classical
  unfold badChecksDistanceOrRectanglesEncoding
  split <;> rfl
end QEC.Coding.ProductExpansion
