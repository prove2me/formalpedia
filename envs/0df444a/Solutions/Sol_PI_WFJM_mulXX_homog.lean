-- Prove2me | solution 1 for PI.WFJM.mulXX_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:05:42.152797+00:00
-- url     : https://prove2.me/submissions/84cfea1b-33dc-4499-af47-415a4606b179

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
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
private theorem isHomogeneous_X_one (k : σ) : (X k : MvPolynomial σ ℂ).IsHomogeneous 1 := by
  first
  | exact isHomogeneous_X ℂ k
  | exact isHomogeneous_X k
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
theorem _root_.solution (l l' : σ) (d : ℕ) (Q : MvPolynomial σ ℂ) (hQ : Q ∈ homog σ d) :
    ((LinearMap.mulLeft ℂ (X l) * LinearMap.mulLeft ℂ (X l') : Module.End ℂ (MvPolynomial σ ℂ)) Q) ∈
      homog σ (d + 2) := by
  have h := (isHomogeneous_X_one l).mul ((isHomogeneous_X_one l').mul ((mem_homogeneousSubmodule d Q).mp hQ))
  rw [show 1 + (1 + d) = d + 2 by omega] at h
  exact (mem_homogeneousSubmodule (d + 2) _).mpr h
end PI.WFJM
