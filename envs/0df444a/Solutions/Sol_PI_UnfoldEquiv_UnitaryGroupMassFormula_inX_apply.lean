-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.inX_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:15:40.242384+00:00
-- url     : https://prove2.me/submissions/46d741f1-8bcc-46d1-9261-b6d9004c9d2f

import Definitions.Def_Formalism_PeriodIntegrals_UnfoldEquiv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
theorem _root_.solution {n c : ℕ} (x : Fin n → k) (l : Fin (n + c)) :
    inX k n c x l = if h : l.1 < n then x ⟨l.1, h⟩ else 0 := by
  simp only [inX, LinearMap.pi_apply]
  split_ifs with h
  · rfl
  · rfl
end PI.UnfoldEquiv.UnitaryGroupMassFormula
