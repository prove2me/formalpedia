-- Prove2me | solution 1 for PI.WfLogWork.coefWf_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:36.854801+00:00
-- url     : https://prove2.me/submissions/d1bad39f-f64f-4d77-bfde-1c3f2db83ef6

import Definitions.Def_Formalism_PeriodIntegrals_InvSerSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_InvNatMemWf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_CoefWfIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfLogWork
open PI.ExpIntWProof
namespace PI.WfLogWork
theorem _root_.solution {p : ℕ} [Fact p.Prime] (f : PowerSeries ℂ_[p]) :
    CoefWf (f : MvPowerSeries Unit ℂ_[p]) ↔ ∀ n, PowerSeries.coeff n f ∈ Wf p := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h n
    have hn : n = Finsupp.single () (n ()) := by
      first
        | exact Finsupp.unique_single n
        | (ext; simp)
    rw [hn]
    exact h (n ())
end PI.WfLogWork
