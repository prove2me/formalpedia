-- Prove2me | solution 1 for PI.OddDualWeyl.jacobiMinorReverse
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:13:31.038347+00:00
-- url     : https://prove2.me/submissions/6333c712-dccc-437a-b7d2-27b98b144887

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacobiMinorIdentity
import Theorems.Thm_PI_OddDualWeyl_Jac_jacobi
import Theorems.Thm_PI_OddDualWeyl_Jac_dualSub_pMinor
import Theorems.Thm_PI_OddDualWeyl_Jac_sign_pm

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
open PI PI.OddDualWeyl
open Jac
namespace PI.OddDualWeyl
theorem _root_.solution : JacRev := by
  unfold JacRev
  intro R _ k s hs
  refine ⟨((Equiv.Perm.sign ((PI.OddDualWeyl.Jac.eR k s hs).trans (PI.OddDualWeyl.Jac.eR k s hs).symm) : ℤ) : R),
    PI.OddDualWeyl.Jac.sign_pm R _, ?_⟩
  calc dualSub R k (pMinor R Fin.revPerm (s + 1) hs)
      = (Matrix.of fun p q : Fin (s + 1) => adjugate (genM R k) (Fin.rev (Fin.castLE hs q))
          ((Fin.revPerm : Equiv.Perm (Fin k)) (Fin.castLE hs p))).det :=
        PI.OddDualWeyl.Jac.dualSub_pMinor R Fin.revPerm (s + 1) hs
    _ = (((adjugate (genM R k)).submatrix (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs)).toBlocks₂₂)ᵀ.det :=
        congrArg Matrix.det (Matrix.ext fun p q => rfl)
    _ = ((adjugate (genM R k)).submatrix (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs)).toBlocks₂₂.det :=
        det_transpose _
    _ = ((Equiv.Perm.sign ((PI.OddDualWeyl.Jac.eR k s hs).trans (PI.OddDualWeyl.Jac.eR k s hs).symm) : ℤ) :
          MvPolynomial (Fin k × Fin k) R) * (genM R k).det ^ (Fintype.card (Fin (s + 1)) - 1) *
          ((genM R k).submatrix (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs)).toBlocks₁₁.det :=
        PI.OddDualWeyl.Jac.jacobi (PI.OddDualWeyl.Jac.eR k s hs) (PI.OddDualWeyl.Jac.eR k s hs) (genM R k)
    _ = C (((Equiv.Perm.sign ((PI.OddDualWeyl.Jac.eR k s hs).trans (PI.OddDualWeyl.Jac.eR k s hs).symm) : ℤ) : R)) *
          (genM R k).det ^ s * pMinor R 1 (k - 1 - s) (by omega) := by
        rw [map_intCast, Fintype.card_fin, Nat.add_sub_cancel, pMinor]
        all_goals rfl
end PI.OddDualWeyl
