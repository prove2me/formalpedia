-- Prove2me | solution 1 for PI.FJMB.aeval_killS_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:37:58.225142+00:00
-- url     : https://prove2.me/submissions/ec484d95-219a-42de-ac66-d2d2470d5a52

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Theorems.Thm_P2M_PI_FJMB_aeval_aeval__e19064defd0d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution {K : Type*} [CommRing K] [Algebra ℂ K] (S : Set σ) (y : σ → K)
    (hy : ∀ v ∈ S, y v = 0) (f : MvPolynomial σ ℂ) : aeval y (aeval (killS S) f) = aeval y f := by
  rw [aeval_aeval']
  congr 2
  funext v
  by_cases h : v ∈ S
  · simp [killS, h, hy v h]
  · simp [killS, h]
end PI.FJMB
