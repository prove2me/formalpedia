-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_expIntegralMvSubst__5afa1a87c868
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:14.869898+00:00
-- url     : https://prove2.me/submissions/03cc01a2-9191-4401-9483-46e79ba589df

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_substMv
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_substMv_mvExp

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
theorem _root_.solution : LGSubstMv := by
  intro K _ _ R σ _ f hf τ a ha
  have ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0 := fun s => (ha s).1
  refine ⟨MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0) ha0 hf.1, ?_⟩
  rw [← substMv_mvExp hf.1 ha0]
  exact intMv_substMv hf.2 ha
end Formalism.L2.Th1.C
