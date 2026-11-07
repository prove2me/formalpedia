-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_one_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:46:32.375735+00:00
-- url     : https://prove2.me/submissions/899d6cbc-1498-4891-8737-dfe4e9aa8b5a

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (Q : R) {n : ℕ} (hn : 0 < n) : qPoch 1 Q n = 0 :=
  Finset.prod_eq_zero (Finset.mem_range.mpr hn) (by simp)
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
