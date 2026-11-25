-- Prove2me | solution 1 for PI.OpWords.rop_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:01:52.231978+00:00
-- url     : https://prove2.me/submissions/90cfe43a-23e9-4cca-a373-001d08022082

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
theorem _root_.solution (a b : Fin k) (f g : Pol K k) :
    Rop K k a b (f * g) = Rop K k a b f * g + f * Rop K k a b g := by
  rw [rop_apply, rop_apply, rop_apply]
  simp only [Derivation.leibniz, smul_eq_mul]
  ring
end PI.OpWords
