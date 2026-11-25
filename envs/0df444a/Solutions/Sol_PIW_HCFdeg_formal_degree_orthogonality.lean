-- Prove2me | solution 1 for PIW.HCFdeg.formal_degree_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:36:52.495641+00:00
-- url     : https://prove2.me/submissions/5e7963af-7df6-4961-a020-bb01ea115b12

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeOrthogonality
import Theorems.Thm_PIW_HCFdeg_irr_repOf

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
theorem _root_.solution : FormalDegreeFromOrthogonality := by
  intro hOrth hUni n ε H _ _ _ _ σ hU hI hSq
  haveI := (hUni n ε).1
  haveI := (hUni n ε).2
  obtain ⟨d, hd, h⟩ := hOrth (UJ ε) (muG ε) H (repOf ε σ hU.1)
    (fun g v => hU.2.1 _ (umat_mem g) v)
    (fun v => (hU.2.2 v).comp_continuous (continuous_coeMatrix ε) umat_mem)
    (irr_repOf ε σ hU.1 hI) (fun v w => hSq v w)
  exact ⟨d, hd, fun v w v' w' => h v w v' w'⟩
end PIW.HCFdeg
