-- Prove2me | solution 1 for PI.Dv.RK.rep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:36:10.055831+00:00
-- url     : https://prove2.me/submissions/ad99ca36-5340-4659-8ce6-9819d1790604

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
namespace PI.Dv.RK
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] (ρ : Representation K G W)
    (z : MonoidAlgebra K G) : ρ.asAlgebraHom z = ∑ g, z.coeff g • ρ g := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply]
  exact Finsupp.sum_fintype _ _ (fun g => zero_smul _ _)
end PI.Dv.RK
