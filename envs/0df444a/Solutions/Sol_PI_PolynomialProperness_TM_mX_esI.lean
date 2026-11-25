-- Prove2me | solution 1 for PI.PolynomialProperness.TM.mX_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:04:33.054921+00:00
-- url     : https://prove2.me/submissions/8c4a7082-297f-4f65-a997-104d3988bef6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
import Theorems.Thm_PI_PolynomialProperness_TM_esI_val

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
    mX k r vX (esI k r a) j =
      if h : r + k < j.val then (vXᴴ)⁻¹ a ⟨2 * r + k - j.val, by omega⟩ else 0 := by
  have ha := a.isLt
  unfold mX
  rw [dif_neg (show ¬ ((esI k r a).val < r) by show ¬ (2 * r + k - a.val < r); omega),
    dif_pos (show r + k < (esI k r a).val by show r + k < 2 * r + k - a.val; omega)]
  by_cases hj : r + k < j.val
  · rw [dif_pos hj, dif_pos hj]
    have e : (⟨2 * r + k - (esI k r a).val, by rw [esI_val]; omega⟩ : Fin r) = a :=
      Fin.ext (by show 2 * r + k - (esI k r a).val = a.val; rw [esI_val]; omega)
    rw [e]
  · rw [dif_neg hj, dif_neg hj]
end PI.PolynomialProperness.TM
