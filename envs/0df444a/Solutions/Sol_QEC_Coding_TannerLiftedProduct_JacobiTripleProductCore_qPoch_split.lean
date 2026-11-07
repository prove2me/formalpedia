-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:10:31.666369+00:00
-- url     : https://prove2.me/submissions/e205812a-2966-473a-a272-2b611bd5b30c

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (A Q : R) (n k : ℕ) :
    qPoch A Q (n + k) = qPoch A Q n * qPoch (A * Q ^ n) Q k := by
  rw [qPoch, qPoch, qPoch, Finset.prod_range_add]
  simp [pow_add, mul_assoc]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
