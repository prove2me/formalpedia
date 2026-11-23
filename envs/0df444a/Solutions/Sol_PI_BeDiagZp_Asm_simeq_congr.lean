-- Prove2me | solution 1 for PI.BeDiagZp.Asm.simeq_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:13.294714+00:00
-- url     : https://prove2.me/submissions/67335c73-f1ba-41ec-bced-fd590fc4e7d6

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
theorem _root_.solution {σ : Type} {f g f' g' : MvPowerSeries σ ℂ_[p]} (e : f - g = f' - g')
    (h : Simeq f g) : Simeq f' g' := by
  unfold Simeq at *
  rw [← e]
  exact h
end PI.BeDiagZp.Asm
