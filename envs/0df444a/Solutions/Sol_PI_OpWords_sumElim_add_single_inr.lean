-- Prove2me | solution 1 for PI.OpWords.sumElim_add_single_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:02:03.587068+00:00
-- url     : https://prove2.me/submissions/bbb526d7-5030-4db8-a76a-304c511286be

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
theorem _root_.solution (m g : Fin k →₀ ℕ) (b : Fin k) :
    Finsupp.sumElim m g + single (Sum.inr b) 1 = Finsupp.sumElim m (g + single b 1) := by
  ext v
  rcases v with i | i <;> simp [Finsupp.single_apply]
end PI.OpWords
