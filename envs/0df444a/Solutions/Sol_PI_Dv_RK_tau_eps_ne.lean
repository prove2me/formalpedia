-- Prove2me | solution 1 for PI.Dv.RK.tau_eps_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:13.192581+00:00
-- url     : https://prove2.me/submissions/e484d1c9-0790-44ee-9cd8-e7ddf2a2f62b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_AsAlgApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.RK
open MonoidAlgebra
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.RK
theorem _root_.solution (T : GoodSet K G) (P : Pair K G) (h : M1 T P) (s : T.S) :
    (T.tau s).asAlgebraHom (eps P) ≠ 0 := by
  intro h0
  have h1 : nS T P s = 1 := h s
  unfold nS at h1
  rw [Submodule.finrank_eq_zero.mpr (by rw [h0]; exact LinearMap.range_zero)] at h1
  exact zero_ne_one h1
end PI.Dv.RK
