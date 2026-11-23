-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.isFillOf_fillMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:48.898202+00:00
-- url     : https://prove2.me/submissions/4313a2a9-51d0-4956-8fc5-826c55f9c96f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_Points
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_Q_iff
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_fillMatrix_single


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
theorem _root_.solution {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' (c + 1) n c → k) : Q xj (xx1 xj t) := by
  rw [Q_iff]
  intro l s h
  rw [fillMatrix_single, dif_neg h]
end PI.UnfoldEquiv.UnitaryGroupMassFormula
