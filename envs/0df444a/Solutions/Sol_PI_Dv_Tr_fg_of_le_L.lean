-- Prove2me | solution 1 for PI.Dv.Tr.fg_of_le_L
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:06.443384+00:00
-- url     : https://prove2.me/submissions/fa6eb445-afae-4cae-b99f-f3a762630fe8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_TraceFormulaOfRankDegree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_FgOfLeL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
namespace PI.Dv.Tr
theorem _root_.solution (A : Formalism.BasicNotions.HLat K) (hA : A.Good) (M : Submodule (𝓞 K) A.V) (hM : M ≤ A.L) : M.FG :=
  isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian A.L hA.2.1) M hM
end PI.Dv.Tr
