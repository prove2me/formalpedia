-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.gh_chArg_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:21.007922+00:00
-- url     : https://prove2.me/submissions/a2db28e4-3f7b-4f1e-9bc4-1901a53d72e4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnfoldingMatrixFreeCoordinate
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_gh_atN_add

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
theorem _root_.solution {n' c' n c : ℕ} (x z : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    chArg (n := n) (c := c) (x + z) = chArg (n := n) (c := c) x + chArg (n := n) (c := c) z := by
  unfold chArg
  simp [LinearMap.add_apply, gh_atN_add, Finset.sum_add_distrib]
end PI.TwistedEisensteinNonvanishing.W
