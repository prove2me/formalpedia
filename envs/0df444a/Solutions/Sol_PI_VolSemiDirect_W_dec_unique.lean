-- Prove2me | solution 1 for PI.VolSemiDirect.W.dec_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:50:36.08829+00:00
-- url     : https://prove2.me/submissions/41123445-e48d-4587-b167-d2c69cc6b734

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
    {n1 n2 : N} {h1 h2 : H} (h : (n1 : X) * (h1 : X) = (n2 : X) * (h2 : X)) :
    n1 = n2 ∧ h1 = h2 := by
  have h1 : e (n1, h1) = e (n2, h2) := Subtype.ext (by rw [he, he]; exact h)
  have h2 := e.injective h1
  exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩
end PI.VolSemiDirect.W
