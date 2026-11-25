-- Prove2me | solution 1 for PI.Dv.RK.L_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:35:43.473294+00:00
-- url     : https://prove2.me/submissions/f1f00f47-ee23-4b09-a09d-e836a15a6267

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_OfMulEps

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
variable {K : Type} [Field K] {σ : K →+* ℂ} {G : Type} [Group G] [Fintype G] {T : GoodSet K G}
  {EE : Type} [AddCommGroup EE] [Module ℂ EE] {ρE : Representation ℂ G EE}
variable (M : GMap K σ G T EE ρE)
namespace PI.Dv.RK
theorem _root_.solution (z : MonoidAlgebra K G) {v : M.V} (hv : v ∈ LinearMap.ker M.io) :
    L M z v ∈ LinearMap.ker M.io := by
  rw [L, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun g _ => ?_
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [LinearMap.mem_ker] at hv ⊢
  rw [M.io_eq, hv, map_zero]
end PI.Dv.RK
