-- Prove2me | solution 1 for PI.QmRowExpWork.cycle_perm_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:06:50.466937+00:00
-- url     : https://prove2.me/submissions/4c9ad21f-2a5b-4687-b05b-7f4dd75165f4

import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowExpansionMinor_FirstColumnSplitBijective

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
theorem _root_.solution (m : ℕ) (j : Fin (m + 1)) (k : Fin m) : cyc0 m j k.succ = j.succAbove k := by
  apply (Fin.cycleRange j).injective
  simp [cyc0, Fin.cycleRange_succAbove]
end PI.QmRowExpWork
