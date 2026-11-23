-- Prove2me | solution 1 for PI.OpWords.sumElim_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:26.686436+00:00
-- url     : https://prove2.me/submissions/7a0007b0-52e2-4b68-a0d5-20f6dad59aee

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
theorem _root_.solution {u g u' g' : Fin k →₀ ℕ} :
    Finsupp.sumElim u g = Finsupp.sumElim u' g' ↔ u = u' ∧ g = g' := by
  constructor
  · intro h
    constructor
    · ext i
      have h1 := congrArg (fun f => f (Sum.inl i)) h
      simpa using h1
    · ext i
      have h1 := congrArg (fun f => f (Sum.inr i)) h
      simpa using h1
  · rintro ⟨rfl, rfl⟩
    rfl
end PI.OpWords
