-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPochhammerInf_eq_tprod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:10:30.750183+00:00
-- url     : https://prove2.me/submissions/3fe965e2-9bfa-470e-bb1d-f0067638e2e8

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (a Q : R)
    (hm : letI := piTop; Multipliable (fun n ↦ 1 - a * Q ^ n)) : letI := piTop;
    qPochhammerInf a Q = ∏' n, (1 - a * Q ^ n) := by
  letI := piTop
  haveI : T2Space R := PowerSeries.WithPiTopology.instT2Space _
  exact tprod_eq_of_multipliable_unconditional hm
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
