-- Prove2me | solution 1 for PI.QmColExpWork.sign_cycle_perm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:11.642276+00:00
-- url     : https://prove2.me/submissions/04cbdd5f-521e-4c8e-98a9-15d726fce50a

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
theorem _root_.solution (m : ℕ) (j : Fin (m + 1)) :
    Equiv.Perm.sign (cyc0 m j) = (-1) ^ (j : ℕ) := by
  unfold cyc0
  rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange]
end PI.QmColExpWork
