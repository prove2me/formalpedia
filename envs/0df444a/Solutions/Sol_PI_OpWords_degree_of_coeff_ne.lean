-- Prove2me | solution 1 for PI.OpWords.degree_of_coeff_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:23.340751+00:00
-- url     : https://prove2.me/submissions/b0e6fb9c-fbca-41f1-9990-5afb9a90a3ef

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
theorem _root_.solution (F : ↥(homogeneousSubmodule (Fin k) K d)) {m : Fin k →₀ ℕ}
    (h : coeff m (F : MvPolynomial (Fin k) K) ≠ 0) : m.degree = d := by
  have hF := (mem_homogeneousSubmodule d _).1 F.2
  rw [Finsupp.degree_eq_weight_one]
  exact hF h
end PI.OpWords
