-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.lhs_coeff_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:51:40.176984+00:00
-- url     : https://prove2.me/submissions/7ae545c1-8bf0-4092-88f6-ef17d251052b

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_factors_multipliable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPochhammerInf_eq_tprod
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_tprod_eq_coeff_qPoch

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m n : ℕ) (hmn : m < n) :
    letI := piTop
    (qPochhammerInf (-x * q) (q ^ 2) : R).coeff m =
    (qPoch (-x * q) (q ^ 2) n : R).coeff m := by
  rw [qPochhammerInf_eq_tprod (-x * q) (q ^ 2) (factors_multipliable x)]
  exact coeff_tprod_eq_coeff_qPoch x m n hmn
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
