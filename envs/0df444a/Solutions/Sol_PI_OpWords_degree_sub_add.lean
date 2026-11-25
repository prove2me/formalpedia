-- Prove2me | solution 1 for PI.OpWords.degree_sub_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:41.328793+00:00
-- url     : https://prove2.me/submissions/0d9a2056-5b96-4032-b443-3b9a453f2fb1

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
theorem _root_.solution (g : Fin k →₀ ℕ) (a b : Fin k) (hb : g b ≠ 0) :
    (g - single b 1 + single a 1).degree = g.degree := by
  have hle : single b 1 ≤ g := by
    rw [Finsupp.single_le_iff]
    omega
  have hs : ∀ c : Fin k, (single c 1 : Fin k →₀ ℕ).degree = 1 := fun c => by
    rw [Finsupp.degree_eq_sum]
    simp [Finsupp.single_apply]
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [map_add, map_add, hs, hs]
end PI.OpWords
