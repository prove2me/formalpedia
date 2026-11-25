-- Prove2me | solution 1 for PI.UD.eval_bind_torusSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:32:47.109847+00:00
-- url     : https://prove2.me/submissions/0c7b2ea2-77f4-4208-b268-5e2ae74bf9ee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_GramStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_EvalBindTorusSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI PI.UD
namespace PI.UD
theorem _root_.solution {ι : Type} {n : ℕ} (w v : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (t : ι × Fin n → ℂ) :
    eval t (bind₁ (torusSubst w v) P) =
      eval (fun x : ι × Fin n × Fin n =>
        (w x.1 * diagonal (fun k => t (x.1, k)) * v x.1) x.2.1 x.2.2) P := by
  refine (eval₂Hom_bind₁ (RingHom.id ℂ) t (torusSubst w v) P).trans
    (congrArg (fun f => eval f P) (funext fun x => ?_))
  rw [Matrix.mul_apply]
  simp [torusSubst, Matrix.mul_diagonal]
end PI.UD
