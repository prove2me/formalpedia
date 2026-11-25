-- Prove2me | solution 1 for PI.VolSemiDirect.W.dec_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:31.24698+00:00
-- url     : https://prove2.me/submissions/ca345107-b23c-4d93-b239-069fb0d14693

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_FundamentalDomainExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_VolumeQuotientHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open MeasureTheory
variable {X : Type} [Group X] [TopologicalSpace X] {K N H : Subgroup X}
namespace PI.VolSemiDirect.W
theorem _root_.solution (e : (N × H) ≃ₜ K) (he : ∀ p : N × H, ((e p : K) : X) = (p.1 : X) * (p.2 : X))
    (k : K) : (k : X) = ((e.symm k).1 : X) * ((e.symm k).2 : X) := by
  have := he (e.symm k)
  rwa [e.apply_symm_apply] at this
end PI.VolSemiDirect.W
