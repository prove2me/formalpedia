-- Prove2me | solution 1 for PI.WMI.lowerInv_coeff_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:10:46.514679+00:00
-- url     : https://prove2.me/submissions/bed67c4a-daa4-4089-9f2f-a55ae5ea4cfe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_LowerInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace
namespace PI.WMI
theorem _root_.solution (p q : Polynomial ℂ) (D u : ℂ) (h : ∀ c, q.eval c = D * p.eval (c * u))
    (m : ℕ) : q.coeff m = D * u ^ m * p.coeff m := by
  have hq : q = Polynomial.C D * p.comp (Polynomial.C u * Polynomial.X) := by
    apply Polynomial.funext
    intro c
    rw [h, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, mul_comm u c]
  rw [hq, Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff]
  ring
end PI.WMI
