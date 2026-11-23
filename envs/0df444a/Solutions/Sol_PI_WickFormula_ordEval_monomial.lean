-- Prove2me | solution 1 for PI.WickFormula.ordEval_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:13.434569+00:00
-- url     : https://prove2.me/submissions/3e1621f6-457e-4841-b5dc-315e46f0e65c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_OrdEvalEqSumOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula
variable {k AA : Type} [CommRing k] [Ring AA] [Algebra k AA] {r s : ℕ}
namespace PI.WickFormula
theorem _root_.solution (a : Fin r → AA) (a' : Fin s → AA) (m : Fin r ⊕ Fin s →₀ ℕ) (c : k) :
    ordEval a a' (monomial m c) = c • omon a a' m := by
  rw [ordEval_eq_sum_of a a' _ {m} MvPolynomial.support_monomial_subset]
  simp [MvPolynomial.coeff_monomial]
end PI.WickFormula
