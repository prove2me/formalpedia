-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.log_le_exponent_of_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:49:05.229205+00:00
-- url     : https://prove2.me/submissions/6d2df6d1-bdc2-4a11-bb31-5eac00feb388

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
theorem _root_.solution
    (q x e : Nat) (hq : 1 < q) (hPower : x ≤ q ^ e) :
    Nat.log q x ≤ e := by
  calc
    Nat.log q x ≤ Nat.log q (q ^ e) := Nat.log_mono_right hPower
    _ = e := Nat.log_pow hq e
end QEC.Coding.TannerLiftedProduct
