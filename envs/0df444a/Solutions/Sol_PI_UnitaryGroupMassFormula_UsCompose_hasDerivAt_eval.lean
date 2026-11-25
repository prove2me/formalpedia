-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:55:22.822622+00:00
-- url     : https://prove2.me/submissions/ae12a029-7b54-4a16-9389-2b733d72b9be

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution {σ : Type*} [Fintype σ] (v : ℝ → σ → ℂ) (v' : σ → ℂ)
    (hv : ∀ i, HasDerivAt (fun t => v t i) (v' i) 0) (q : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => eval (v t) q) (∑ i, eval (v 0) (pderiv i q) * v' i) 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simpa [pderiv_C] using hasDerivAt_const (0 : ℝ) a
  | add p q hp hq =>
    have hf : (fun t => eval (v t) (p + q)) = fun t => eval (v t) p + eval (v t) q := by
      funext t; simp
    rw [hf]
    refine (hp.add hq).congr_deriv ?_
    simp [map_add, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have hf : (fun t => eval (v t) (p * X i)) = fun t => eval (v t) p * v t i := by
      funext t; simp
    rw [hf]
    refine (hp.mul (hv i)).congr_deriv ?_
    symm
    · simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, eval_X, pderiv_X, add_mul,
        Finset.sum_add_distrib]
      rw [show ∀ a b c d : ℂ, b = c → a = d → a + b = c + d from
        fun a b c d h1 h2 => by rw [h1, h2, add_comm]]
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      · simp [Pi.single_apply, apply_ite (eval (v 0)), mul_ite, ite_mul, Finset.sum_ite_eq,
          Finset.sum_ite_eq']
end PI.UnitaryGroupMassFormula.UsCompose
