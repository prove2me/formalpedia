-- Prove2me | solution 1 for PI.BeDiagZp.Asm.ccX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:07.893427+00:00
-- url     : https://prove2.me/submissions/d3885df4-1256-467e-8cd7-4af84ea20c02

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SimeqCongr

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
open PI PI.BeDiagZp
open PI.BeDiagZp.Asm
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.Asm
theorem _root_.solution {σ : Type} (i : σ) : MvPowerSeries.constantCoeff (Xv i : MvPowerSeries σ ℂ_[p]) = 0 := by
  simp [Xv]
end PI.BeDiagZp.Asm
