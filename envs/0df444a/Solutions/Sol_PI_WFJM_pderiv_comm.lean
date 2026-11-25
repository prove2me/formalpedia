-- Prove2me | solution 1 for PI.WFJM.pderiv_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:48.370037+00:00
-- url     : https://prove2.me/submissions/4fdaaf66-d84c-4c1f-a676-5e0f9b440217

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM
open MvPolynomial
open PI.FJM
open MvPolynomial
variable {σ : Type*}
namespace PI.WFJM
theorem _root_.solution (i j : σ) (P : MvPolynomial σ ℂ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  have h : ⁅pderiv (R := ℂ) i, pderiv (R := ℂ) j⁆ = (0 : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) := by
    apply derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h2 : ⁅pderiv (R := ℂ) i, pderiv (R := ℂ) j⁆ P =
      (0 : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) P := by rw [h]
  rw [Derivation.commutator_apply] at h2
  have h3 : (0 : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) P = 0 := by simp
  exact sub_eq_zero.mp (h2.trans h3)
end PI.WFJM
