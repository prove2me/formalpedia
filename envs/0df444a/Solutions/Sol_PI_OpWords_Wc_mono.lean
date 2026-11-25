-- Prove2me | solution 1 for PI.OpWords.Wc_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:04:42.109876+00:00
-- url     : https://prove2.me/submissions/c89986b4-3244-4df2-9785-dd385965e6da

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PairingPowMemSymbolRange

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
theorem _root_.solution {c c' : ℕ} (h : c ≤ c') : Wc K k d c ≤ Wc K k d c' := by
  unfold Wc
  apply Submodule.span_mono
  rintro Bx ⟨l, hl, rfl⟩
  exact ⟨l, le_trans hl h, rfl⟩
end PI.OpWords
