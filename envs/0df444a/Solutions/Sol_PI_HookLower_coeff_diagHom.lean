-- Prove2me | solution 1 for PI.HookLower.coeff_diagHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:59:43.984893+00:00
-- url     : https://prove2.me/submissions/06dd8074-e8f6-4024-86ba-8bf604149c02

import Definitions.Def_Formalism_PeriodIntegrals_HookBound
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
import Theorems.Thm_PI_HookLower_diagHom_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookLower
namespace PI.HookLower
theorem _root_.solution {N : ℕ} (f : MvPolynomial (Fin N × Fin N) ℚ) (m : Fin N × Fin N →₀ ℕ)
    (hm : IsDiag m) : coeff m (diagHom N f) = coeff m f := by
  classical
  refine MvPolynomial.induction_on' f (fun μ c => ?_) (fun p q hp hq => ?_)
  · rw [diagHom_monomial]
    split_ifs with h
    · rfl
    · rw [coeff_zero, coeff_monomial, if_neg]
      rintro rfl
      exact h hm
  · rw [map_add, coeff_add, coeff_add, hp, hq]
end PI.HookLower
