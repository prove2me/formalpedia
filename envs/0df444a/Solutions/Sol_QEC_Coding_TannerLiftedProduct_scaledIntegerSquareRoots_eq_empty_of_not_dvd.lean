-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.scaledIntegerSquareRoots_eq_empty_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:39:06.997464+00:00
-- url     : https://prove2.me/submissions/9e0d567e-6242-46da-b55a-07ac6c71a207

import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.RingTheory.PowerSeries.Substitution
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceTheta
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {m n : ℕ} (hm : 0 < m) (hdiv : ¬ m ^ 2 ∣ n) :
    scaledIntegerSquareRoots m n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  apply hdiv
  refine ⟨z.natAbs ^ 2, ?_⟩
  rw [mem_scaledIntegerSquareRoots_iff hm] at hz
  rw [← Nat.cast_inj (R := ℤ)]
  push_cast
  simpa [sq_abs] using hz.symm
end QEC.Coding.TannerLiftedProduct
