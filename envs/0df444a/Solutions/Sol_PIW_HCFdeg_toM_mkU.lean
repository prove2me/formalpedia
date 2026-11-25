-- Prove2me | solution 1 for PIW.HCFdeg.toM_mkU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:22:01.016099+00:00
-- url     : https://prove2.me/submissions/21589cdc-b2db-431f-9862-8be0e0ee6779

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
theorem _root_.solution (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) : toM (mkU ε g hg) = g := rfl
end PIW.HCFdeg
