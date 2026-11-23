-- Prove2me | solution 1 for PI.BeDiagZp.Asm.intX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:08.074809+00:00
-- url     : https://prove2.me/submissions/3afbcc63-f116-4761-b806-405b86557886

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
theorem _root_.solution {σ : Type} (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := by
  intro n
  simp only [IsIntP, Xv, MvPowerSeries.coeff_X]
  split_ifs <;> simp
end PI.BeDiagZp.Asm
