-- Prove2me | solution 1 for PI.QnCovHat2W.sum_fun_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:56:58.554583+00:00
-- url     : https://prove2.me/submissions/d42cd7a0-c32e-428a-b731-c3ffe93dcde7

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_SkipTwoOfGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open PI PI.QnCovHat2W
open Formalism.REAL Formalism.FourierDecayAlt.Q
namespace PI.QnCovHat2W
theorem _root_.solution {r : ℕ} {α : Type*} [Fintype α] [DecidableEq α] {M : Type*} [AddCommMonoid M]
    (f : (Fin (r + 1) → α) → M) :
    ∑ x, f x = ∑ x0 : α, ∑ y : Fin r → α, f (Fin.cons x0 y) := by
  rw [← (Fin.consEquiv fun _ : Fin (r + 1) => α).sum_comp, Fintype.sum_prod_type]
  rfl
end PI.QnCovHat2W
