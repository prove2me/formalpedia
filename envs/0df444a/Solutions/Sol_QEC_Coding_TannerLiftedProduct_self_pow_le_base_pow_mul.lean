-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.self_pow_le_base_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:51:45.66175+00:00
-- url     : https://prove2.me/submissions/a243aecd-d4cc-4681-9ed8-b7027c881c4b

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_self_le_base_pow

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
theorem _root_.solution (q n a : Nat) (hq : 2 ≤ q) :
    n ^ a ≤ q ^ (n * a) := by
  calc
    n ^ a ≤ (q ^ n) ^ a :=
      Nat.pow_le_pow_left (self_le_base_pow q n hq) a
    _ = q ^ (n * a) := by rw [← pow_mul]
end QEC.Coding.TannerLiftedProduct
