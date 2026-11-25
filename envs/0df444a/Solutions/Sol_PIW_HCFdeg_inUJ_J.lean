-- Prove2me | solution 1 for PIW.HCFdeg.inUJ_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:24:11.724905+00:00
-- url     : https://prove2.me/submissions/1c361b5d-d744-4145-99ba-f38b494fc59d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod

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
theorem _root_.solution : inUJ ε (Jm ε) := by
  unfold inUJ Jm
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]
end PIW.HCFdeg
