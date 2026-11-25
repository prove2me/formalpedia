-- Prove2me | solution 1 for PIW.HCFdeg.isCompact_KG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:38:04.732206+00:00
-- url     : https://prove2.me/submissions/6024b785-b7d5-4036-a84f-dbdd8af3d3cd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_Unimod
import Theorems.Thm_PIW_HCFdeg_isCompact_Kset

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
theorem _root_.solution : IsCompact ((KG ε : Set (UJ ε))) :=
  (isClosedEmbeddingMatrix n ε).1.isCompact_preimage (isCompact_Kset ε)
end PIW.HCFdeg
