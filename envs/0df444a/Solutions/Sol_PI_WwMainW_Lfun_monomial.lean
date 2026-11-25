-- Prove2me | solution 1 for PI.WwMainW.Lfun_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:14:52.07636+00:00
-- url     : https://prove2.me/submissions/6b042c70-1b2d-41de-ba10-06e6642fb164

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_FintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionMinors_LfunEqOfSubset
import Theorems.Thm_PI_WwMainW_Lfun_eq_of_subset

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
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (α : (Lt × Fin N0 × Fin N1) →₀ ℕ) (c : ℂ_[l]) :
    Lfun l N0 N1 Th (monomial α c) = c * wt l N0 N1 Th α := by
  classical
  rw [Lfun_eq_of_subset l N0 N1 Th _ {α} MvPolynomial.support_monomial_subset]
  simp
end PI.WwMainW
