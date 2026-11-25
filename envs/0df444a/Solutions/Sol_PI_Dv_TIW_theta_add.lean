-- Prove2me | solution 1 for PI.Dv.TIW.theta_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:06.526312+00:00
-- url     : https://prove2.me/submissions/27d681f3-2d78-4539-b093-47a86b511c31

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
theorem _root_.solution (M N : Module.End K (T.W s)) : theta T s (M + N) = theta T s M + theta T s N := by
  simp [theta, mul_add, add_smul, Finset.sum_add_distrib]
end PI.Dv.TIW
