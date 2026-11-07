-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.a_pow_eq_C_T
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:48:12.146198+00:00
-- url     : https://prove2.me/submissions/2e3907aa-54dc-4796-89a0-ac2a4070b1e3

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (k : ℕ) :
    (a : R) ^ k = PowerSeries.C (LaurentPolynomial.T (k : ℤ)) := by
  calc (a : R) ^ k
      = (PowerSeries.C (LaurentPolynomial.T 1) : R) ^ k := rfl
    _ = PowerSeries.C ((LaurentPolynomial.T 1) ^ k) := by rw [map_pow]
    _ = _ := by rw [LaurentPolynomial.T_pow]; simp
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
