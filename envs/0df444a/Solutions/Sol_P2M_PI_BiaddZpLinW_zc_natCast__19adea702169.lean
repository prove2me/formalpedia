-- Prove2me | solution 1 for P2M_PI_BiaddZpLinW_zc_natCast__19adea702169
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:53:32.972+00:00
-- url     : https://prove2.me/submissions/64d275f8-72a9-43b5-955e-ecf43f28ddd8

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
theorem _root_.solution (n : ℕ) : zc (n : ℤ_[p]) = (n : ℂ_[p]) := by
  simp [zc]
end PI.BiaddZpLinW
