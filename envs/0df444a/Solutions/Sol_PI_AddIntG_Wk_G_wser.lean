-- Prove2me | solution 1 for PI.AddIntG.Wk.G_wser
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:37.158642+00:00
-- url     : https://prove2.me/submissions/0b224b9b-cfd1-4469-9bcc-4e3ba0485644

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_GuLine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS

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
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    G W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) = 0 := by
  simp only [IsWq] at h
  unfold G wser
  rw [sub_eq_zero]
  conv_rhs => rw [h]
  ring
end PI.AddIntG.Wk
