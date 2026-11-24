-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_expIntegralDeriv__70ca0e7dcf2b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:35:19.159212+00:00
-- url     : https://prove2.me/submissions/e6a5deb6-57d6-49f4-8998-592874b99045

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_mul
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_pderiv
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_constantCoeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_pderiv_mvExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open IntegralMvPolynomialLemmas
namespace Formalism.L2.Th1.C
theorem _root_.solution : LGDeriv := by
  intro K _ _ R σ f hf i
  have h0 := constantCoeff_mvExp hf.1
  have hne : MvPowerSeries.constantCoeff (mvExp f) ≠ 0 := by rw [h0]; exact one_ne_zero
  have hinv : mvExp f * (mvExp f)⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ hne
  have hV : IntMv R (mvExp f)⁻¹ := intMv_of_mul_eq_one hf.2 h0 hinv
  have : MvPowerSeries.pderiv K i f = (mvExp f)⁻¹ * MvPowerSeries.pderiv K i (mvExp f) := by
    rw [pderiv_mvExp hf.1, ← mul_assoc, mul_comm _ (mvExp f), hinv, one_mul]
  rw [this]
  exact intMv_mul hV (intMv_pderiv hf.2 i)
end Formalism.L2.Th1.C
