-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.reindex_Z_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:29:30.373375+00:00
-- url     : https://prove2.me/submissions/b4ec271d-1357-40c7-b253-acf5d6e62a8e

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_lhs_eq_g_comp_reindex

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution : letI := piTop;
    (∑' p : ℤ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 - ↑p.2)) *
      ((-1 : R) ^ p.2 * q ^ (p.1.natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) =
    (∑' p : ℤ × ℕ,
      PowerSeries.C (LaurentPolynomial.T p.1) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + ↑p.2).natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) := by
  letI := piTop
  simp_rw [lhs_eq_g_comp_reindex]
  change (∑' p : ℤ × ℕ, g (reindexEquiv p)) = ∑' p : ℤ × ℕ, g p
  exact @Equiv.tsum_eq R _ _ _ piTop reindexEquiv g
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
