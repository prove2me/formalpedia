-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_succ__251408f0b858
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:08:47.863856+00:00
-- url     : https://prove2.me/submissions/89c70315-8006-42de-ab21-376f4117c952

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution {R' : Type*} [CommRing R'] (A Q : R') (n : ℕ) :
    qPoch A Q (n + 1) = qPoch A Q n * (1 - A * Q ^ n) := by
  simp [qPoch, Finset.prod_range_succ, mul_comm]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
