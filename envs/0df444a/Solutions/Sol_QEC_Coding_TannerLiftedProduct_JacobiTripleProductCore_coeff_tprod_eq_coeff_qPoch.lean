-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_tprod_eq_coeff_qPoch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:49:34.92157+00:00
-- url     : https://prove2.me/submissions/aa300abb-a010-4656-aae7-1118589c8352

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_factors_multipliable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_partial_prods_coeff_stable

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (m n : ℕ) (hmn : m < n) :
    letI := piTop
    ((∏' i, (1 - (-x * q) * (q ^ 2) ^ i : R)) : R).coeff m =
    (qPoch (-x * q) (q ^ 2) n : R).coeff m := by
  letI := piTop
  exact tendsto_nhds_unique
    ((PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto
      (LaurentPolynomial ℤ) _ _ _).mp (factors_multipliable x).tendsto_prod_tprod_nat m)
    (tendsto_atTop_of_eventually_const (i₀ := n) (fun k hk =>
      partial_prods_coeff_stable x m n k hmn hk))
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
