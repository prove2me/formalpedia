-- Prove2me | solution 1 for PIW.HCFdeg.modChar_UJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:49:08.00652+00:00
-- url     : https://prove2.me/submissions/6c5aeb46-93e8-4cfc-b093-b0e21f7d6289

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
import Theorems.Thm_PIW_HCFdeg_modChar_eq_one_of_compact
import Theorems.Thm_PIW_HCFdeg_modChar_herm
import Theorems.Thm_PIW_HCFdeg_isCompact_KG
import Theorems.Thm_PIW_HCFdeg_polar

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
variable {n : ℕ} (ε : Fin n → Bool)
namespace PIW.HCFdeg
theorem _root_.solution [T2Space (UJ ε)] (g : UJ ε) : Measure.modularCharacter g = 1 := by
  obtain ⟨s, hs, hk⟩ := polar ε g
  have h1 := modChar_eq_one_of_compact (muG ε) (KG ε) (isCompact_KG ε) _ hk
  have h2 := modChar_herm ε s hs
  have e : g = (g * s⁻¹) * s := by group
  rw [e, map_mul, h1, h2, mul_one]
end PIW.HCFdeg
