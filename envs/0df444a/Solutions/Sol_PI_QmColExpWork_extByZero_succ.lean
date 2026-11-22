-- Prove2me | solution 1 for PI.QmColExpWork.extByZero_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:34.889703+00:00
-- url     : https://prove2.me/submissions/8652a822-56a7-43d4-a75e-4a215c08f06d

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
theorem _root_.solution {m : ℕ} (τ : Equiv.Perm (Fin m)) (k : Fin m) : ext0 τ k.succ = (τ k).succ := by
  simp [ext0]
end PI.QmColExpWork
