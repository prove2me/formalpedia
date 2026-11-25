-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.gh_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:36:51.253456+00:00
-- url     : https://prove2.me/submissions/55174e46-93e7-4dc9-9e77-ab2ccc578486

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnfoldingMatrixFreeCoordinate
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_gh_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution {M N : ℕ} (f : (Fin M → E) →ₗ[E] (Fin N → E)) (v : Fin M → E) (l : Fin N) :
    f v l = ∑ m : Fin M, v m * f (eN E M m.1) l := by
  conv_lhs => rw [gh_decomp v]
  simp [map_sum, Finset.sum_apply, mul_comm]
end PI.TwistedEisensteinNonvanishing.W
