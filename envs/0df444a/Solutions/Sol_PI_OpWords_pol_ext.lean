-- Prove2me | solution 1 for PI.OpWords.pol_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:40:03.377098+00:00
-- url     : https://prove2.me/submissions/b33ad2f1-2e98-472e-a8f5-7fbd234d77f3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaCoeff
import Theorems.Thm_PI_OpWords_exists_sumElim

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
theorem _root_.solution {P Q : Pol K k}
    (h : ∀ m g : Fin k →₀ ℕ, coeff (Finsupp.sumElim m g) P = coeff (Finsupp.sumElim m g) Q) : P = Q := by
  ext n
  obtain ⟨m, g, rfl⟩ := exists_sumElim n
  exact h m g
end PI.OpWords
