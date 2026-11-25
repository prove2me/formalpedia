-- Prove2me | solution 1 for PI.Dv.RK.L_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:39:50.985465+00:00
-- url     : https://prove2.me/submissions/9e9b23e3-53b8-49d5-b15b-39da2108f4b0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_OfMulEps
import Theorems.Thm_PI_Dv_RK_rep_apply

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
theorem _root_.solution (z : MonoidAlgebra K G) (x : M.VK) :
    L M z (M.j x) = M.j (M.rhoK.asAlgebraHom z x) := by
  simp only [L, rep_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
    LinearMap.map_smulₛₗ, M.j_eq]
end PI.Dv.RK
