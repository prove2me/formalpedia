-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.rank_singleRowMatrix_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:00:40.131204+00:00
-- url     : https://prove2.me/submissions/8562d9ee-ed37-4b64-99b2-c0ce44999457

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
omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (c : Word F W) (hc : c ≠ 0) : (singleRowMatrix c).rank = 1 := by
  rw [Matrix.rank_eq_finrank_span_row, Set.range_unique]
  change Module.finrank F (F ∙ c) = 1
  exact finrank_span_singleton hc
end QEC.Coding.ProductExpansion
