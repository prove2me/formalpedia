-- Prove2me | solution 1 for PI.IsoDerivBFintype.Q_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:28.498932+00:00
-- url     : https://prove2.me/submissions/c4a676cf-6345-4d53-84c3-c18fd26f5674

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDerivB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ExistsOePerm
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDerivative_ApplyAt0EqSum
import Theorems.Thm_PI_IsoDerivBFintype_eval_mY

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.IsoDerivBFintype
open PI.IsoDerivB
variable {Lt T : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) {N N' : ℕ}
  (nu : Lt → YoungDiagram)
variable [Fintype T]
namespace PI.IsoDerivBFintype
theorem _root_.solution (φ : LaC N nu) (Q : MvPolynomial (FrV T N) ℂ)
    (hQ : ∀ y, evFr Q y = canC φ (frC tp y)) :
    Q = ∑ J, MvPolynomial.C (φ J) * mY tp nu J := by
  apply MvPolynomial.funext
  intro x
  let y : T → Matrix (Fin N) (Fin N) ℂ := fun τ => Matrix.of fun a b => x (τ, a, b)
  have h1 : evFr Q y = MvPolynomial.eval x Q := rfl
  have h2 : ∀ J, MvPolynomial.eval x (mY tp nu J) = minY N nu J (frC tp y) := fun J =>
    eval_mY tp nu J y
  rw [← h1, hQ, map_sum]
  simp only [map_mul, MvPolynomial.eval_C, h2]
  unfold canC prC hvC
  rw [finsum_eq_sum_of_fintype]
end PI.IsoDerivBFintype
