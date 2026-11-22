-- Prove2me | solution 1 for PI.QmColExpWork.matrixExtendByZero_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:39.680391+00:00
-- url     : https://prove2.me/submissions/9dd550f4-7eba-4a25-b437-6a2897bc6331

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
theorem _root_.solution {m : ℕ} (τ : Equiv.Perm (Fin m)) : ext0 τ 0 = 0 := by
  simp [ext0]
end PI.QmColExpWork
