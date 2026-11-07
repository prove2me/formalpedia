-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.per_term_simplify
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:45.653841+00:00
-- url     : https://prove2.me/submissions/a53ffbf7-95aa-4d2b-b4e7-9c37c65b048b

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_mul_invOfUnit_cancel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPochhammerInf_split

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (k : ℕ) : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) =
    q ^ (k ^ 2) * x ^ k *
      qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) := by
  letI := piTop
  rw [qPochhammerInf_split k]
  calc qPoch (q ^ 2) (q ^ 2) k * qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) *
        (q ^ k ^ 2 * x ^ k * (qPoch (q ^ 2) (q ^ 2) k).invOfUnit 1)
      = q ^ k ^ 2 * x ^ k * qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) *
        (qPoch (q ^ 2) (q ^ 2) k * (qPoch (q ^ 2) (q ^ 2) k).invOfUnit 1) := by ring
    _ = _ := by rw [qPoch_mul_invOfUnit_cancel, mul_one]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
