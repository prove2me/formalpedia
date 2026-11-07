-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.ring_rearrangement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:49.563839+00:00
-- url     : https://prove2.me/submissions/6174c7c7-e336-421c-8d57-aa3ffa21451a

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (Q : R) (n k : ℕ)
    (P_n P_k P_nk1 a b : R)
    (ih1 : a * P_k * (P_nk1 * (1 - Q * Q ^ (n - (k + 1)))) = P_n)
    (ih2 : b * (P_k * (1 - Q * Q ^ k)) * P_nk1 = P_n)
    (h_alg : (1 - Q * Q ^ k) + Q ^ (k + 1) * (1 - Q * Q ^ (n - (k + 1))) = 1 - Q * Q ^ n) :
    (a + Q ^ (k + 1) * b) *
      (P_k * (1 - Q * Q ^ k)) *
      (P_nk1 * (1 - Q * Q ^ (n - (k + 1)))) =
    P_n * (1 - Q * Q ^ n) := by
  grind
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
