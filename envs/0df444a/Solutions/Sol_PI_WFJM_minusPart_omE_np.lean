-- Prove2me | solution 1 for PI.WFJM.minusPart_omE_np
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:35:53.358057+00:00
-- url     : https://prove2.me/submissions/4ed70e7f-00c7-4df2-852c-262affe717cc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_omE_ne
import Theorems.Thm_PI_WFJM_minusPart_lower
import Theorems.Thm_PI_WFJM_hc_dd
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
private theorem raiB_eq_neg_pderiv_of_not_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) : FockH1Action.raiB l = -(pderiv l).toLinearMap := by
  rw [FockH1Action.raiB, if_neg (show ¬ (FockH1Action.linePos l = true) by simp [h])]
private theorem lowB_eq_pderiv_of_linePos {p q r s : ℕ} {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) : FockH1Action.lowB l = (pderiv l).toLinearMap := by
  rw [FockH1Action.lowB, if_pos h]
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
theorem _root_.solution {p q r s : ℕ} (l l' : Ln p q r s) (h : linePos l = false) (h' : linePos l' = true)
    (P : Pol p q r s) : minusPart (omE l l') P = -(dd l l' P) := by
  have hne : l ≠ l' := ne_of_linePos (by rw [h, h']; decide)
  have hop : FockH1Action.omE l l' = -PI.FJM.dd l l' := by
    rw [omE_ne hne, raiB_eq_neg_pderiv_of_not_linePos h, lowB_eq_pderiv_of_linePos h', PI.FJM.dd, neg_mul]
  rw [hop]
  have hL : ∀ (e : ℕ) (Q : FockH1Action.Pol p q r s),
      MvPolynomial.homogeneousComponent e ((-PI.FJM.dd l l') Q) =
        (-PI.FJM.dd l l') (MvPolynomial.homogeneousComponent (e + 2) Q) := by
    intro e Q
    rw [LinearMap.neg_apply, LinearMap.neg_apply, map_neg, hc_dd]
  rw [minusPart_lower _ hL, LinearMap.neg_apply]
end PI.WFJM
