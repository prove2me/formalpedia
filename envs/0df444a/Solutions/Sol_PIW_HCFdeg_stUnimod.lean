-- Prove2me | solution 1 for PIW.HCFdeg.stUnimod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:05.0886+00:00
-- url     : https://prove2.me/submissions/952ece3e-1a07-4683-8c01-15b5d447f7e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
import Theorems.Thm_PIW_HCFdeg_unimod_of_modChar
import Theorems.Thm_PIW_HCFdeg_modChar_UJ

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
open MeasureTheory PI.UpqRep Matrix
open scoped MatrixOrder NNReal ENNReal ComplexOrder Pointwise
namespace PIW.HCFdeg
theorem _root_.solution : StUnimod := by
  unfold StUnimod
  intro n ε
  exact unimod_of_modChar (muG ε) (fun g => modChar_UJ ε g)
end PIW.HCFdeg
