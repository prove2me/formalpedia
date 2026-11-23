-- Prove2me | solution 1 for PI.Dv.TIW.theta_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:30.620335+00:00
-- url     : https://prove2.me/submissions/cf13d3d5-212d-48fd-aec3-7d780fb4ef39

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)
namespace PI.Dv.TIW
theorem _root_.solution : theta T s 1 = eS T s := by simp [theta, eS]
end PI.Dv.TIW
