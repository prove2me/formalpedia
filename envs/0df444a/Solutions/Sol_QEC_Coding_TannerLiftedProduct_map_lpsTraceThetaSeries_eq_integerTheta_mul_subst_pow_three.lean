-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.map_lpsTraceThetaSeries_eq_integerTheta_mul_subst_pow_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:43:42.711463+00:00
-- url     : https://prove2.me/submissions/9254eff4-de95-4095-8382-145a6ffc5be4

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_map_scaledIntegerThetaSeries_eq_subst
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {q : ℕ} (hq : 0 < q) :
    (lpsTraceThetaSeries q).map (Nat.castRingHom ℤ) =
      integerThetaSeries.map (Nat.castRingHom ℤ) *
        (PowerSeries.subst
          (PowerSeries.X ^ ((2 * q) ^ 2))
          (integerThetaSeries.map (Nat.castRingHom ℤ))) ^ 3 := by
  rw [lpsTraceThetaSeries_eq_integerTheta_mul_scaled_pow_three hq,
    map_mul, map_pow,
    map_scaledIntegerThetaSeries_eq_subst (by omega : 0 < 2 * q)]
end QEC.Coding.TannerLiftedProduct
