-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_polynomial_lt_rank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:07:47.927799+00:00
-- url     : https://prove2.me/submissions/82369287-8af4-4e78-85f8-4c2af35abc96

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleExponent_polynomial_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_24
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (A B n q : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hn : 0 < n)
    (hThreshold : 8 * A + 26 < B * n) :
    coarseRectangleExponent (A * n ^ 6) (n ^ 4) (n ^ 7) q + 3 <
      n ^ 5 * (B * n ^ 6) := by
  calc
    coarseRectangleExponent (A * n ^ 6) (n ^ 4) (n ^ 7) q + 3 ≤
        (8 * A + 26) * n ^ 10 :=
      coarseRectangleExponent_polynomial_le A n q hq hA hn
    _ < (B * n) * n ^ 10 :=
      (Nat.mul_lt_mul_right (Nat.pow_pos hn)).2 hThreshold
    _ = n ^ 5 * (B * n ^ 6) := by ring
end QEC.Coding.TannerLiftedProduct
