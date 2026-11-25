-- Prove2me | solution 1 for PI.OddDualWeyl.LowA.prod_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:04:56.107009+00:00
-- url     : https://prove2.me/submissions/16ec2f6e-7d96-42ee-86a2-025340b6d47d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightDualOf
import Theorems.Thm_PI_OddDualWeyl_LowA_expo_castSucc
import Theorems.Thm_PI_OddDualWeyl_LowA_expo_star_last
import Theorems.Thm_PI_OddDualWeyl_LowA_expo_last
import Theorems.Thm_PI_OddDualWeyl_Low_pMinor_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.LowA
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.LowA
theorem _root_.solution {m : ℕ} (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) (σ : Equiv.Perm (Fin (m + 1))) :
    ∏ s : Fin (m + 1), pMinor R σ (m + 1 - 1 - s.val) (by omega) ^
      (nuOf (lamStar lam) s - nuNext (nuOf (lamStar lam)) s) = pw R σ (nuOf lam) := by
  rw [PI.OddDualWeyl.pw, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, expo_star_last,
    expo_last]
  simp only [pow_zero, mul_one]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun s => ?_)
  have hr : (Fin.revPerm s : Fin m) = s.rev := rfl
  rw [hr, expo_castSucc lam hlam s]
  congr 1
  have hs := s.isLt
  exact PI.OddDualWeyl.Low.pMinor_congr σ (by simp only [Fin.val_castSucc, Fin.val_rev]; omega) _ _
end PI.OddDualWeyl.LowA
