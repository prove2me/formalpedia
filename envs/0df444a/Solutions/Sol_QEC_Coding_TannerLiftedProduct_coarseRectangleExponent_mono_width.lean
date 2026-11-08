-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_mono_width
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:50:32.165665+00:00
-- url     : https://prove2.me/submissions/b04e8cac-613c-44ef-9a4f-cc49698b52d0

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
    (w w' m s q : Nat) (hWidth : w ≤ w') :
    coarseRectangleExponent w m s q ≤
      coarseRectangleExponent w' m s q := by
  have hSquare : w * w + 1 ≤ w' * w' + 1 := by gcongr
  have hLog : Nat.log q (w * w + 1) ≤ Nat.log q (w' * w' + 1) :=
    Nat.log_mono_right hSquare
  unfold coarseRectangleExponent
  gcongr
end QEC.Coding.TannerLiftedProduct
