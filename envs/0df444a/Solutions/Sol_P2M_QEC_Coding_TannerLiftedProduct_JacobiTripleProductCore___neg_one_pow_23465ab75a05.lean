-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___neg_one_pow_23465ab75a05
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:54:04.563486+00:00
-- url     : https://prove2.me/submissions/49ef20f1-87d1-40bf-af9f-d5d54e3ee971

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (ℓ : ℕ) :
    ι_hahn ((-1 : R) ^ ℓ) = HahnSeries.single (0 : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) := by
  rw [map_pow, map_neg, map_one]
  change (-1) ^ ℓ = _
  rw [show (-1 : S_hahn) = HahnSeries.single (0 : ℤ) (-1 : LaurentPolynomial ℤ) by
    rw [← HahnSeries.C_apply]
    simp]
  rw [HahnSeries.single_pow, smul_zero]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
