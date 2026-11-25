-- Prove2me | solution 1 for PI.WFJM.minusPart_omE_pn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:15.468791+00:00
-- url     : https://prove2.me/submissions/6eeb1f92-b02a-4556-abdf-b8d4a7ae08d8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_omE_ne
import Theorems.Thm_PI_WFJM_minusPart_raise
import Theorems.Thm_PI_WFJM_mulXX_homog
import Theorems.Thm_PI_WFJM_ne_of_linePos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix FockH1Action
namespace PI.WFJM
end PI.WFJM
namespace PI.WFJM
open MvPolynomial
private theorem raiB_eq_mulLeft_X_of_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) : FockH1Action.raiB l = LinearMap.mulLeft ℂ (X l) := by
  rw [FockH1Action.raiB, if_pos h]
private theorem lowB_eq_mulLeft_X_of_not_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) : FockH1Action.lowB l = LinearMap.mulLeft ℂ (X l) := by
  rw [FockH1Action.lowB, if_neg (show ¬ (FockH1Action.linePos l = true) by simp [h])]
open PI.FJM
section Grade
open MvPolynomial
variable {σ : Type*}
end Grade
section Lap
variable {p q r s : ℕ}
end Lap
section HW
variable {p q r s : ℕ}
open MvPolynomial
end HW
end PI.WFJM
namespace PI.FJM
end PI.FJM
end
end

set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
namespace PI.WFJM
theorem _root_.solution {p q r s : ℕ} (l l' : Ln p q r s) (h : linePos l = true) (h' : linePos l' = false)
    (P : Pol p q r s) : minusPart (omE l l') P = 0 := by
  have hne : l ≠ l' := ne_of_linePos (by rw [h, h']; decide)
  rw [omE_ne hne, raiB_eq_mulLeft_X_of_linePos h, lowB_eq_mulLeft_X_of_not_linePos h']
  apply minusPart_raise
  intro d Q hQ
  exact mulXX_homog l l' d Q hQ
end PI.WFJM
