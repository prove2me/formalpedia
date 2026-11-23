-- Prove2me | solution 1 for PI.BeDiagZp.ContPf.cc_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:08.28083+00:00
-- url     : https://prove2.me/submissions/cec13ae8-868c-4b87-ac7d-d4e49ffd1b8b

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
theorem _root_.solution {σ : Type} : CC fun c : ℂ_[p] => (MvPowerSeries.C c : MvPowerSeries σ ℂ_[p]) := by
  intro n
  simp only [MvPowerSeries.coeff_C]
  by_cases h : n = 0
  · simp only [h, if_true]; exact continuous_id
  · simp only [h, if_false]; exact continuous_const
end PI.BeDiagZp.ContPf
