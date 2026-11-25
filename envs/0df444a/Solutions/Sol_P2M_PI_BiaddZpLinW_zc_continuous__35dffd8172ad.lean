-- Prove2me | solution 1 for P2M_PI_BiaddZpLinW_zc_continuous__35dffd8172ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:46:07.549042+00:00
-- url     : https://prove2.me/submissions/6df2007e-e36c-4583-bbcf-5ce6fc4788c3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_Cont2
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BiadditivePadicLinear_BiadditiveContinuousPadic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BiaddZpLinW
open PI.BiaddZpLin PI.BeDiagZp.ContPf
variable {p : ℕ} [Fact p.Prime]
namespace PI.BiaddZpLinW
theorem _root_.solution : Continuous (zc : ℤ_[p] → ℂ_[p]) := by
  unfold zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val
end PI.BiaddZpLinW
