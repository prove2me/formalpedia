-- Prove2me | solution 1 for PI.PolynomialProperness.TM.sig_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:04:00.662078+00:00
-- url     : https://prove2.me/submissions/7a6bb9e7-5e65-45ab-93af-6de12f8f171d

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
theorem _root_.solution (k r : ℕ) (t : Fin r) : GBasic.sig k r (eI k r t) = esI k r t := by
  have h : (eI k r t).val < r ∨ r + k < (eI k r t).val := Or.inl t.isLt
  unfold GBasic.sig
  rw [if_pos h]
  rfl
end PI.PolynomialProperness.TM
