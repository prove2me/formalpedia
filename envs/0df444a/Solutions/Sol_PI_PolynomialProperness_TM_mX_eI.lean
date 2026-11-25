-- Prove2me | solution 1 for PI.PolynomialProperness.TM.mX_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:36.704003+00:00
-- url     : https://prove2.me/submissions/5c9a513f-2032-48d8-ae54-fbec2c9e4ac3

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
theorem _root_.solution (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    mX k r vX (eI k r a) j = if h : j.val < r then vX a ⟨j.val, h⟩ else 0 := by
  unfold mX
  rw [dif_pos (show (eI k r a).val < r from a.isLt)]
  rfl
end PI.PolynomialProperness.TM
