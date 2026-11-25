-- Prove2me | solution 1 for PI.FockOneDegW.Diag.fockAct1_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:43.575687+00:00
-- url     : https://prove2.me/submissions/cd267e2a-4304-4365-a86e-8beb7819f17a

import Definitions.Def_Formalism_PeriodIntegrals_FockDegreeTwoParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_OmEDiagMonomial
import Theorems.Thm_PI_FockOneDegW_Diag_omE_diag_monomial
import Theorems.Thm_PI_FockOneDegW_Diag_fockAct1_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockH1Action
open PI PI.FockOneDegW PI.FockOneDegW.Diag
namespace PI.FockOneDegW.Diag
theorem _root_.solution (p q r s : ℕ) (a : Ix p q) (β : Ln p q r s →₀ ℕ) :
    fockAct1 p q r s (Eab a a) (MvPolynomial.monomial β (1 : ℂ)) =
      ((W1 a β : ℚ) : ℂ) • MvPolynomial.monomial β (1 : ℂ) := by
  rw [fockAct1_diag, LinearMap.sum_apply]
  simp only [omE_diag_monomial, W1, Rat.cast_sum, Finset.sum_smul]
end PI.FockOneDegW.Diag
