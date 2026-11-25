-- Prove2me | solution 1 for PI.WFJM.minusPart_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:24.76368+00:00
-- url     : https://prove2.me/submissions/c6580767-7e73-40e1-9ae9-582b9bba24c7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Theorems.Thm_PI_WFJM_hc_hc
import Theorems.Thm_PI_WFJM_eq_zero_of_hc
import Theorems.Thm_PI_WFJM_minusPart_eq_sum
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
open PI.FJM
section Grade
open MvPolynomial
variable {σ : Type*}
private theorem homogeneousComponent_minusPart (A : Module.End ℂ (MvPolynomial σ ℂ))
    (P : MvPolynomial σ ℂ) (e : ℕ) :
    homogeneousComponent e (FockH1Action.minusPart A P) =
      homogeneousComponent e (A (homogeneousComponent (e + 2) P)) := by
  rw [minusPart_eq_sum, map_sum]
  simp only [hc_hc]
  first
  | rw [Finset.sum_ite_eq]
  | rw [Finset.sum_ite_eq']
  by_cases h : e ∈ Finset.range (P.totalDegree + 1)
  · rw [if_pos h]
  · rw [if_neg h]
    rw [Finset.mem_range, not_lt] at h
    rw [homogeneousComponent_eq_zero (e + 2) P (by omega), map_zero, map_zero]
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
open MvPolynomial
variable {σ : Type*}
namespace PI.WFJM
theorem _root_.solution (L : Module.End ℂ (MvPolynomial σ ℂ))
    (hL : ∀ (e : ℕ) (P : MvPolynomial σ ℂ),
      homogeneousComponent e (L P) = L (homogeneousComponent (e + 2) P))
    (P : MvPolynomial σ ℂ) : minusPart L P = L P := by
  rw [← sub_eq_zero]
  apply eq_zero_of_hc
  intro e
  rw [map_sub, homogeneousComponent_minusPart, hL, hL,
    hc_hc, if_pos rfl, sub_self]
end PI.WFJM
