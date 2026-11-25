-- Prove2me | solution 1 for PI.VolSemiDirect.W.symm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:54:15.353171+00:00
-- url     : https://prove2.me/submissions/7717f3da-e291-4547-b00d-71434bdc295d

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
    {k : K} {n : N} {h : H} (hk : (k : X) = (n : X) * (h : X)) : e.symm k = (n, h) := by
  rw [e.symm_apply_eq]
  exact Subtype.ext (by rw [he]; exact hk)
end PI.VolSemiDirect.W
