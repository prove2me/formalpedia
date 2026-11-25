-- Prove2me | solution 1 for PI.PolynomialProperness.TM.midF_mX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:42:04.368333+00:00
-- url     : https://prove2.me/submissions/87324b16-83e3-4ee5-9409-850ec68c199c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_TauDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_MXMulVecMid
import Theorems.Thm_PI_PolynomialProperness_TM_mX_mulVec_mid

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
theorem _root_.solution (k r : ℕ) (vX : Matrix (Fin r) (Fin r) ℂ) (x y : Fin (2 * r + k + 1) → ℂ) :
    midF k r (mX k r vX *ᵥ x) (mX k r vX *ᵥ y) = midF k r x y := by
  unfold midF
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rw [mX_mulVec_mid k r vX x i h.1 h.2, mX_mulVec_mid k r vX y i h.1 h.2]
  · rfl
end PI.PolynomialProperness.TM
