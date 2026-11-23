-- Prove2me | solution 1 for PI.BeDiagZp.ContPf.cc_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:30.857534+00:00
-- url     : https://prove2.me/submissions/53c528aa-74b5-4cef-b180-8f12680b076e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_ConstantCoeffSubstEqZero

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
open PI PI.BeDiagZp PI.BeDiagZp.ContPf
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.ContPf
theorem _root_.solution {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : CC fun _ : ℂ_[p] => F :=
  fun _ => continuous_const
end PI.BeDiagZp.ContPf
