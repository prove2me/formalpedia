-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.factor_coeff_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:18:36.313223+00:00
-- url     : https://prove2.me/submissions/a364bd0d-e3e4-4d25-b896-c8feed503cbb

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (x : R) (j i : ℕ) (hji : j < 1 + 2 * i) :
    (1 - (-x * q) * (q ^ 2) ^ i : R).coeff j = if j = 0 then 1 else 0 := by
  have h_key : ∀ (x : R) (k : ℕ), j < k → (x * q ^ k).coeff j = 0 :=
    fun _ _ h => by grind only [coeff_mul_X_pow']
  have h_expr : (-x * q : R) * (q ^ 2 : R) ^ i = -x * (q : R) ^ (2 * i + 1 : ℕ) := by ring
  simp_all [show j < 2 * i + 1 by nlinarith]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
