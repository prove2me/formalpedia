-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.atN_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:51.876811+00:00
-- url     : https://prove2.me/submissions/fb4bc098-3459-44e6-ae05-1368c9cff341

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
theorem _root_.solution {N : ℕ} (a : k) (v : Fin N → k) (i : ℕ) : atN (a • v) i = a * atN v i := by
  simp only [atN]
  split_ifs <;> simp
end PI.UnfoldEquiv.UnitaryGroupMassFormula
