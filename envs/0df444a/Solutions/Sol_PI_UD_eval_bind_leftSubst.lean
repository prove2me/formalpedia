-- Prove2me | solution 1 for PI.UD.eval_bind_leftSubst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:32:43.861041+00:00
-- url     : https://prove2.me/submissions/5fe64f12-308d-4982-b085-a11cb4e81b1e

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
theorem _root_.solution {ι : Type} {n : ℕ} (A : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (u : ι → Matrix (Fin n) (Fin n) ℂ) :
    eval (fun x : ι × Fin n × Fin n => u x.1 x.2.1 x.2.2) (bind₁ (leftSubst A) P) =
      eval (fun x : ι × Fin n × Fin n => (A x.1 * u x.1) x.2.1 x.2.2) P := by
  refine (eval₂Hom_bind₁ (RingHom.id ℂ) _ (leftSubst A) P).trans
    (congrArg (fun f => eval f P) (funext fun x => ?_))
  simp [leftSubst, Matrix.mul_apply]
end PI.UD
