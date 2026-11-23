-- Prove2me | solution 1 for PI.QmColExpWork.cycle_perm_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:10.88808+00:00
-- url     : https://prove2.me/submissions/bfcd4665-f62f-4f19-b295-2badfe888535

import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFirstColumn_FirstColumnSplitBijective

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
open PI PI.QmColExpWork
open Formalism.REAL
namespace PI.QmColExpWork
theorem _root_.solution (m : ℕ) (j : Fin (m + 1)) (k : Fin m) : cyc0 m j k.succ = j.succAbove k := by
  unfold cyc0
  first
  | exact Fin.cycleRange_symm_succ j k
  | rw [Equiv.symm_apply_eq, Fin.cycleRange_succAbove]
end PI.QmColExpWork
