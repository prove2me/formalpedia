-- Prove2me | solution 1 for PI.Dv.GLP.eigen_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:23.592432+00:00
-- url     : https://prove2.me/submissions/a8c61d8f-54f2-45e9-93f7-b345b8951574

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ArithmeticCylinders
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionLattices_IsIntegralTraceOfPow
import Theorems.Thm_UpperTheory_Reformulated_B_ArithmeticCylinders_eigen_pow_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.GLP
open Polynomial
namespace PI.Dv.GLP
theorem _root_.solution {L : Type} [Field L] {d : Type} [Fintype d] [DecidableEq d]
    (M : Matrix d d L) (n : ℕ) (hM : M ^ n = 1) (μ : L) (hμ : M.charpoly.IsRoot μ) : μ ^ n = 1 :=
  _root_.UpperTheory.Reformulated.B.ArithmeticCylinders.eigen_pow_eq_one M n hM μ hμ
end PI.Dv.GLP
