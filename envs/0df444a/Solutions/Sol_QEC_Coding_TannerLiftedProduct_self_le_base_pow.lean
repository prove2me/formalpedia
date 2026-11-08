-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.self_le_base_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:49:03.69353+00:00
-- url     : https://prove2.me/submissions/0aa59391-cc94-4f8c-a97a-49ccdc854b9b

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds

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
theorem _root_.solution (q n : Nat) (hq : 2 ≤ q) : n ≤ q ^ n := by
  calc
    n ≤ 2 * n := by omega
    _ ≤ 2 ^ n := Nat.mul_le_pow (by decide) n
    _ ≤ q ^ n := Nat.pow_le_pow_left hq n
end QEC.Coding.TannerLiftedProduct
