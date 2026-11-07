-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.isUnit_qPoch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:11:30.026045+00:00
-- url     : https://prove2.me/submissions/898964e7-4efa-4fea-8a7e-cb40937136f0

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_constantCoeff_qPoch_eq_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (m : ℕ) : IsUnit (qPoch (q ^ 2) (q ^ 2) m : R) := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_qPoch_eq_one]
  exact isUnit_one
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
