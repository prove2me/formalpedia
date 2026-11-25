-- Prove2me | solution 1 for PI.BeDiagZp.SubstW.integral_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:23.357866+00:00
-- url     : https://prove2.me/submissions/8b38ed4c-1f2b-49cb-a558-5d75f8950b3b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_PowerSeriesDiagonalLinear
import Theorems.Thm_PI_BeDiagZp_SubstW_mem_SerS

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
open PI PI.BeDiagZp PI.BeDiagZp.SubstW
namespace PI.BeDiagZp.SubstW
theorem _root_.solution {p : ℕ} [Fact p.Prime] {σ : Type*} (f : MvPowerSeries σ ℂ_[p]) :
    IntegralMv f ↔ f ∈ SerS (Rint p) σ := by
  rw [mem_SerS]
  exact Iff.rfl
end PI.BeDiagZp.SubstW
