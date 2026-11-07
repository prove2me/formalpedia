-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_A_hahn_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:15:05.148734+00:00
-- url     : https://prove2.me/submissions/70ee101e-9aab-44d1-8c94-5761f73bf6ff

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j : ℕ) (F_arg : S_hahn) (b : ℤ) :
    (A_hahn j * F_arg).coeff b = F_arg.coeff (b + 2 * ↑j) := by
  unfold A_hahn
  conv_lhs => rw [show b = (b + 2 * ↑j) + (-2 * ↑j) by ring]
  rw [HahnSeries.coeff_single_mul_add]
  simp
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
