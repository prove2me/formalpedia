-- Prove2me | solution 1 for PI.OpWords.exists_sumElim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:23.383742+00:00
-- url     : https://prove2.me/submissions/7169ace9-ac52-4f7b-b2ed-e7e6e0569c68

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
theorem _root_.solution (n : Fin k ⊕ Fin k →₀ ℕ) : ∃ m g : Fin k →₀ ℕ, n = Finsupp.sumElim m g := by
  refine ⟨Finsupp.comapDomain Sum.inl n Sum.inl_injective.injOn,
    Finsupp.comapDomain Sum.inr n Sum.inr_injective.injOn, ?_⟩
  ext v
  rcases v with i | i <;> simp [Finsupp.comapDomain_apply]
end PI.OpWords
