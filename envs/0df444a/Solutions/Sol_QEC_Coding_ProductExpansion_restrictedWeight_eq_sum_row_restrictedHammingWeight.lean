-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.restrictedWeight_eq_sum_row_restrictedHammingWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:03:32.708797+00:00
-- url     : https://prove2.me/submissions/f743e325-02c0-4001-9fb0-c6079ee4e45f

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [Fintype F] [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (x : Matrix W W F) (A B : Finset W) :
    restrictedWeight x A B =
      ∑ i ∈ A, restrictedHammingWeight B (row x i) := by
  rfl
end QEC.Coding.ProductExpansion
