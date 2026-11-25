-- Prove2me | solution 1 for PI.WwMainW.applyQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:19:17.241987+00:00
-- url     : https://prove2.me/submissions/8d35feb4-8fe6-4b87-b20c-43e26a2b88e3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_InfinitePadicComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open PI PI.WwMainW
open PI.WwMain PI.WwMain.KM
namespace PI.WwMainW
theorem _root_.solution {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (Q : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l])
    (y' : Lt → Fin N1 → ℕ → ℂ_[l]) :
    applyQ l N0 N1 Th Q y' = Lfun l N0 N1 Th (aeval (fun v : Lt × Fin N0 × ℕ => ∑ b : Fin N1,
      C (y' v.1 b v.2.2) * X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1)) Q) := by
  unfold applyQ Lfun wt
  exact Finset.sum_congr rfl fun α _ => by ring
end PI.WwMainW
