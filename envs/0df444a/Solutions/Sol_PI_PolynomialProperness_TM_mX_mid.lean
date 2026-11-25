-- Prove2me | solution 1 for PI.PolynomialProperness.TM.mX_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:03:55.276888+00:00
-- url     : https://prove2.me/submissions/8148741d-dcb2-4d5e-8c8a-73697409a43f

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
theorem _root_.solution (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (i j : Fin (2 * r + k + 1))
    (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) : mX k r vX i j = if i = j then 1 else 0 := by
  unfold mX
  rw [dif_neg (show ¬ (i.val < r) by omega), dif_neg (show ¬ (r + k < i.val) by omega)]
end PI.PolynomialProperness.TM
