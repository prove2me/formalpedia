-- Prove2me | solution 1 for PI.OpWords.mono_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:38.026918+00:00
-- url     : https://prove2.me/submissions/386d7886-748a-42c4-9756-a8b43c042756

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
variable {K : Type} [Field K] {k d : ℕ}
namespace PI.OpWords
theorem _root_.solution (g : Fin k →₀ ℕ) :
    (mono K k d g : MvPolynomial (Fin k) K) = if g.degree = d then monomial g 1 else 0 := by
  unfold mono
  split_ifs <;> rfl
end PI.OpWords
