-- Prove2me | solution 1 for P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___factor_eq_03466fa1241f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:54:24.060631+00:00
-- url     : https://prove2.me/submissions/9239fec2-8354-40f8-b13a-ade0bae79a39

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (ℓ : ℕ) :
    ι_hahn (1 - q ^ (2 * (↑ℓ + 1))) = 1 - Q₀ ^ (ℓ + 1) := by
  rw [map_sub, map_one]
  congr 1
  show (HahnSeries.ofPowerSeries ℤ (LaurentPolynomial ℤ)) (PowerSeries.X ^ (2 * (↑ℓ + 1))) = _
  rw [HahnSeries.ofPowerSeries_X_pow, show Q₀ = HahnSeries.single (2 : ℤ) 1 from rfl,
    HahnSeries.single_pow]
  simp [add_mul, mul_comm]
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
