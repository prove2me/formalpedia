-- Prove2me | solution 1 for PI.QmRowExpWork.expLastRow_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:16.299224+00:00
-- url     : https://prove2.me/submissions/50ce0cab-7231-40cb-a9db-40afd220642c

import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowExpansionMinor_FirstColumnSplitBijective
import Theorems.Thm_PI_QmRowExpWork_rowLast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.QmRowExpWork
open Formalism.REAL
namespace PI.QmRowExpWork
theorem _root_.solution (h : PI.RowForm) : PI.ExpLastRow := by
  intro A _ _ n t E hE a b u
  rw [h A n (t + 1) E hE a b u, rowLast]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h A n t E hE]
end PI.QmRowExpWork
