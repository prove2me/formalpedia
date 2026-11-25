-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_expIntegralBinomial__c14a18ad148f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:12.621891+00:00
-- url     : https://prove2.me/submissions/a4e8db41-5cdb-40a4-9870-90756c78bd42

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_CoeffPowEqZeroOfCc
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffSubstBinomSeries
import Theorems.Thm_Formalism_L2_Th1_C_subst_binomSeries_eq_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_constantCoeff_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_one
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_subst
import Theorems.Thm_Formalism_L2_Th1_C_constantCoeff_mvExp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
variable {K : Type} [Field K] [CharZero K] {σ : Type}
namespace Formalism.L2.Th1.C
theorem _root_.solution : LGBinom := by
  intro K _ _ R σ z hz f hf
  refine ⟨by rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf.1, mul_zero], ?_⟩
  rw [← subst_binomSeries_eq_mvExp z hf.1]
  refine IntegralMvPolynomialLemmas.intMv_subst (fun n => ?_) ⟨?_, fun n => ?_⟩
  · rw [binomSeries, PowerSeries.coeff_mk]
    exact hz n
  · rw [map_sub, constantCoeff_mvExp hf.1, map_one, sub_self]
  · rw [map_sub]
    exact R.sub_mem (hf.2 n) (IntegralMvPolynomialLemmas.intMv_one n)
end Formalism.L2.Th1.C
