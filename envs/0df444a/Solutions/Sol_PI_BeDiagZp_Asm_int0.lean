-- Prove2me | solution 1 for PI.BeDiagZp.Asm.int0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:13.216344+00:00
-- url     : https://prove2.me/submissions/da59b357-8137-4fd0-b441-1652ee5f359c

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
theorem _root_.solution {σ : Type} : IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := by
  intro n
  simp [IsIntP]
end PI.BeDiagZp.Asm
