-- Prove2me | solution 1 for PI.OpWords.rop_rop_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:56.853845+00:00
-- url     : https://prove2.me/submissions/24739b31-53b5-4677-a3db-7023e4cfc98f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_VanishExp
import Theorems.Thm_PI_OpWords_rop_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords
theorem _root_.solution (a b : Fin k) (hab : a ≠ b) (i : Fin k ⊕ Fin k) :
    Rop K k a b (Rop K k a b (X i)) = 0 := by
  rcases i with j | j
  · by_cases h : j = b
    · subst h
      simp [rop_apply, pderiv_X, Pi.single_apply, hab, Ne.symm hab]
    · simp [rop_apply, pderiv_X, Pi.single_apply, h, Ne.symm h]
  · by_cases h : j = a
    · subst h
      simp [rop_apply, pderiv_X, Pi.single_apply, hab, Ne.symm hab]
    · simp [rop_apply, pderiv_X, Pi.single_apply, h, Ne.symm h]
end PI.OpWords
