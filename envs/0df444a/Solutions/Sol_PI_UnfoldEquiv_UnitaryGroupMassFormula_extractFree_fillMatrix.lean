-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.extractFree_fillMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:03.460037+00:00
-- url     : https://prove2.me/submissions/9dbd6528-01c9-4524-a20c-9ed342a19725

import Definitions.Def_Formalism_PeriodIntegrals_UnfoldEquiv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix
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
theorem _root_.solution {n' n c : ℕ} (xj : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : FC n' (c + 1) n c → k) :
    fe (xx1 xj t) = t := by
  funext p
  show xx1 xj t (Pi.single p.1.2 1) p.1.1 = t p
  rw [fillMatrix_single, dif_pos p.2]
end PI.UnfoldEquiv.UnitaryGroupMassFormula
