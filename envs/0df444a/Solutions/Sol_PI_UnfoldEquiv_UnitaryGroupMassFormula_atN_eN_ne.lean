-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.atN_eN_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:32:46.672701+00:00
-- url     : https://prove2.me/submissions/f3078e18-804c-4aa8-96a8-2cc50243e300

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
theorem _root_.solution {N i j : ℕ} (h : j ≠ i) : atN (eN k N j) i = 0 := by
  unfold atN
  split_ifs with hi
  · rw [eN_apply]
    exact if_neg fun e => h e.symm
  · rfl
end PI.UnfoldEquiv.UnitaryGroupMassFormula
