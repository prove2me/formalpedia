-- Prove2me | solution 1 for PI.FJMX.leadingMinor_rightRootDerivation_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:02:22.808806+00:00
-- url     : https://prove2.me/submissions/3f4661e4-2071-465e-acf7-d0ccbccf77e3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
import Theorems.Thm_PI_FJMX_rightRootDerivation_X
import Theorems.Thm_PI_FJMX_leadT_der_cols

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s : ℕ}
variable {m k : ℕ}
namespace PI.FJMX
theorem _root_.solution (x y : Ix r s) (hxy : x ≠ y) (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (t : ℕ) (hneg : ∀ i, linePos (ρ i, x) = false)
    (hcl : ∀ j₀ : Fin k, j₀.val < t → κ j₀ = x → ∃ j₁ : Fin k, j₁.val < t ∧ κ j₁ = y) :
    der2 x y (leadT (varMat ρ κ) t) = 0 := by
  apply leadT_der_cols
  intro j₀ hj₀
  by_cases hx : κ j₀ = x
  · right
    obtain ⟨j₁, hj₁, hy⟩ := hcl j₀ hj₀ hx
    refine ⟨j₁, hj₁, fun e => hxy (by rw [← hx, ← hy, e]), -1, fun i _ => ?_⟩
    rw [rightRootDerivation_X]
    simp [hneg i, hy, hx]
  · left
    intro i _
    rw [rightRootDerivation_X]
    simp [hneg i, hx]
end PI.FJMX
