-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPochhammerInf_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:52:04.504194+00:00
-- url     : https://prove2.me/submissions/63eba7b2-e6d5-4213-bbf0-fbbeee2675e2

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPochhammerInf_eq_tprod
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_multipliable_factors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_multipliable_shifted
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tprod_split_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k : ℕ) : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) =
    qPoch (q ^ 2) (q ^ 2) k *
    qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) := by
  letI := piTop
  rw [qPochhammerInf_eq_tprod _ _ multipliable_factors, tprod_split_eq k,
      qPochhammerInf_eq_tprod _ _ (multipliable_shifted k)]
  rfl
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
