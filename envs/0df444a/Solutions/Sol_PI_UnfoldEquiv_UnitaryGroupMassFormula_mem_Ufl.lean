-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.mem_Ufl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:49.194795+00:00
-- url     : https://prove2.me/submissions/50f63739-9c6a-4749-893b-95aacd7b345e

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
theorem _root_.solution {n c i : ℕ} {v : Fin (n + c) → k} :
    v ∈ Ufl k n c i ↔ ∀ l : Fin (n + c), ¬ (l.1 < n + i) → v l = 0 := Iff.rfl
end PI.UnfoldEquiv.UnitaryGroupMassFormula
