-- Prove2me | solution 1 for PI.OpWords.pairingPowMemSymbolRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:40.495347+00:00
-- url     : https://prove2.me/submissions/9d1c27bd-88ab-4eec-aeb4-4e27aa3a6ad2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PairingPowMemSymbolRange
import Theorems.Thm_PI_OpWords_mem_Sc
import Theorems.Thm_PI_OpWords_bihom_le_Sc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
variable (K : Type) [Field K] [CharZero K] (k d : ℕ)
namespace PI.OpWords
theorem _root_.solution : Surj := by
  intro K _ _ k d c hc g hg
  exact (mem_Sc K k d c g).1 (bihom_le_Sc K k d c hc hg)
end PI.OpWords
