-- Prove2me | solution 1 for PIW.HCFdeg.hCFdeg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:55.395089+00:00
-- url     : https://prove2.me/submissions/6fd7b516-443c-4495-b905-be265155077c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_HCFdeg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.HCFdeg
open MeasureTheory PI.UpqRep
open scoped InnerProductSpace
namespace PIW.HCFdeg
theorem _root_.solution (h1 : StableSubspaceMobius) (h23 : FormalDegreeValue) : PI.HCFdeg := by
  intro n ε
  obtain ⟨c, hc, h⟩ := h23 n ε
  refine ⟨c, hc, fun lam H _ _ _ σ hl hσ => ?_⟩
  haveI : Nontrivial H := hσ.2.1
  obtain ⟨d, hd⟩ := h1 n ε H σ hσ.2.2.1 hσ.2.2.2.1 hσ.2.2.2.2.1
  rw [← h lam H σ hl hσ d hd]
  exact hd
end PIW.HCFdeg
