-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_coeffsInSubst__336769595df3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:51:10.953349+00:00
-- url     : https://prove2.me/submissions/d9d78340-cb7d-443c-935b-dadbb58e3397

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_subst

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
theorem _root_.solution : IntSubst := by
  intro K _ R f hf σ a ha
  exact intMv_subst hf ha
end Formalism.L2.Th1.C
