-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___expression_eq_single_mul_V_dfa183ee7d29
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:39:56.699284+00:00
-- url     : https://prove2.me/submissions/6fcc2e7b-b9c5-4803-8e9d-8bdd78e70af5

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
import Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___neg_one_pow_23465ab75a05

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (j ℓ : ℕ) :
    let N_val := (-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ
    ι_hahn ((-1 : R) ^ ℓ * q ^ N_val * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    HahnSeries.single (↑N_val : ℤ) ((-1 : LaurentPolynomial ℤ) ^ ℓ) * V ℓ := by
  intro N_val
  rw [map_mul, map_mul, ι_neg_one_pow]
  have hq : ι_hahn (q ^ N_val) = HahnSeries.single (↑N_val : ℤ) 1 :=
    HahnSeries.ofPowerSeries_X_pow N_val
  rw [hq, HahnSeries.single_mul_single, zero_add, mul_one]
  rfl
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
