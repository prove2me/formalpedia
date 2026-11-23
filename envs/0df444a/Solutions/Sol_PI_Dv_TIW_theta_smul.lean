-- Prove2me | solution 1 for PI.Dv.TIW.theta_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:30.926595+00:00
-- url     : https://prove2.me/submissions/8bf762c3-9fa8-456a-9022-775ec43e814e

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
theorem _root_.solution (c : K) (M : Module.End K (T.W s)) : theta T s (c • M) = c • theta T s M := by
  simp only [theta, Finset.smul_sum, smul_smul, mul_smul_comm, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring_nf
end PI.Dv.TIW
