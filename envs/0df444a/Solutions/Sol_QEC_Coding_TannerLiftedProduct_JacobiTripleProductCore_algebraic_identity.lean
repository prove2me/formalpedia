-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.algebraic_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:47.208788+00:00
-- url     : https://prove2.me/submissions/b1d68d75-e901-4d7e-9e0f-ec0d57b86e08

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (Q : R) (n k : ℕ) (hk : k < n) :
    (1 - Q * Q ^ k) + Q ^ (k + 1) * (1 - Q * Q ^ (n - (k + 1))) = 1 - Q * Q ^ n := by
  have h1 : Q ^ (k + 1) * (Q * Q ^ (n - (k + 1))) = Q ^ (n + 1) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  rw [show Q * Q ^ k = Q ^ (k + 1) by rw [← pow_succ'],
    show Q * Q ^ n = Q ^ (n + 1) by rw [← pow_succ'],
    show Q ^ (k + 1) * (1 - Q * Q ^ (n - (k + 1))) = Q ^ (k + 1) - Q ^ (n + 1) by
      rw [mul_sub, mul_one, h1]]
  ring
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
