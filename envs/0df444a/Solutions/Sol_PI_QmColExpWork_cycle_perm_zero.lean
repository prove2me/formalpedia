-- Prove2me | solution 1 for PI.QmColExpWork.cycle_perm_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:29.409595+00:00
-- url     : https://prove2.me/submissions/9960999c-a82e-4c4d-86a1-8a14e7c5f523

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
theorem _root_.solution (m : ℕ) (j : Fin (m + 1)) : cyc0 m j 0 = j := by
  unfold cyc0
  first
  | exact Fin.cycleRange_symm_zero j
  | rw [Equiv.symm_apply_eq, Fin.cycleRange_self]
end PI.QmColExpWork
