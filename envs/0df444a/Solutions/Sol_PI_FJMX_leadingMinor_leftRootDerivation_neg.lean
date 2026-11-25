-- Prove2me | solution 1 for PI.FJMX.leadingMinor_leftRootDerivation_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:36.487014+00:00
-- url     : https://prove2.me/submissions/58b96762-ddfb-414c-a0c0-5fca099d3534

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
import Theorems.Thm_PI_FJMX_leftRootDerivation_X
import Theorems.Thm_PI_FJMX_leadT_der_rows

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
theorem _root_.solution (x y : Ix p q) (hxy : x ≠ y) (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (t : ℕ) (hneg : ∀ j, linePos (x, κ j) = false)
    (hcl : ∀ i₀ : Fin m, i₀.val < t → ρ i₀ = x → ∃ i₁ : Fin m, i₁.val < t ∧ ρ i₁ = y) :
    der1 x y (leadT (varMat ρ κ) t) = 0 := by
  apply leadT_der_rows
  intro i₀ hi₀
  by_cases hx : ρ i₀ = x
  · right
    obtain ⟨i₁, hi₁, hy⟩ := hcl i₀ hi₀ hx
    refine ⟨i₁, hi₁, fun e => hxy (by rw [← hx, ← hy, e]), -1, fun j _ => ?_⟩
    rw [leftRootDerivation_X]
    simp [hneg j, hy, hx]
  · left
    intro j _
    rw [leftRootDerivation_X]
    simp [hneg j, hx]
end PI.FJMX
