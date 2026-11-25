-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.atN_eN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:32:39.988911+00:00
-- url     : https://prove2.me/submissions/b8e1f1ef-82b8-4838-a909-c3c7be0bcd01

import Definitions.Def_Formalism_PeriodIntegrals_UnfoldEquiv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix
import Theorems.Thm_PI_UnfoldEquiv_UnitaryGroupMassFormula_eN_apply

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
theorem _root_.solution {N i : ℕ} (h : i < N) : atN (eN k N i) i = 1 := by
  rw [atN, dif_pos h, eN_apply]
  exact if_pos rfl
end PI.UnfoldEquiv.UnitaryGroupMassFormula
