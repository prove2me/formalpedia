-- Prove2me | solution 1 for PI.Dv.RK.L_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:45:25.76721+00:00
-- url     : https://prove2.me/submissions/d70a0018-1117-483b-952f-217cb222db36

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalKernels_OfMulEps
import Theorems.Thm_PI_Dv_RK_L_j

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
theorem _root_.solution (a b : MonoidAlgebra K G) : L M (a * b) = L M a * L M b :=
  LinearMap.ext_on_range M.j_span fun x => by
    rw [Module.End.mul_apply, L_j, L_j, L_j, map_mul, Module.End.mul_apply]
end PI.Dv.RK
