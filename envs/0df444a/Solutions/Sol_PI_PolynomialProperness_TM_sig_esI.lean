-- Prove2me | solution 1 for PI.PolynomialProperness.TM.sig_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:04:06.17212+00:00
-- url     : https://prove2.me/submissions/f5ec0d9f-8ca0-42fa-a045-28a7d562d6f6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.TM
namespace PI.PolynomialProperness.TM
theorem _root_.solution (k r : ℕ) (t : Fin r) : GBasic.sig k r (esI k r t) = eI k r t := by
  have ht := t.isLt
  have h : (esI k r t).val < r ∨ r + k < (esI k r t).val := by
    right
    show r + k < 2 * r + k - t.val
    omega
  unfold GBasic.sig
  rw [if_pos h]
  apply Fin.ext
  show 2 * r + k - (2 * r + k - t.val) = t.val
  omega
end PI.PolynomialProperness.TM
