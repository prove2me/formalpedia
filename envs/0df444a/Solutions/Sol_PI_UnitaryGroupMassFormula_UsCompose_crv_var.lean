-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.crv_var
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:54:30.9206+00:00
-- url     : https://prove2.me/submissions/f0ee001b-69cf-41c4-a59d-add7c8695bdc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_hasDerivAt


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
theorem _root_.solution {k r : ℕ} (X g : Mat k r) (i : Vr (2 * r + k + 1)) :
    HasDerivAt (fun t => vars (crv (false, X) g t) i) (eval (vars g) (lin X i)) 0 := by
  have h := crv_hasDerivAt (false, X) g
  have hab : ∀ a b, HasDerivAt (fun t => crv (false, X) g t a b) ((g * X) a b) 0 := by
    intro a b
    have h1 := hasDerivAt_pi.1 h a
    have h2 := hasDerivAt_pi.1 h1 b
    simpa [dirv] using h2
  rcases i with ⟨a, b⟩ | ⟨a, b⟩
  · refine (hab a b).congr_deriv ?_
    simp only [lin, map_sum, map_mul, eval_C, eval_X, vars, Sum.elim_inl, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  · refine (hab a b).star.congr_deriv ?_
    simp only [lin, map_sum, map_mul, eval_C, eval_X, vars, Sum.elim_inr, Matrix.mul_apply, star_sum, star_mul']
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
end PI.UnitaryGroupMassFormula.UsCompose
