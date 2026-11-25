-- Prove2me | solution 1 for PI.OddDualWeyl.Low.pw_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:43:36.482126+00:00
-- url     : https://prove2.me/submissions/31fea377-20c9-4ea6-a9e0-f27a92584622

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Theorems.Thm_PI_OddDualWeyl_Low_rowDiv_mem
import Theorems.Thm_PI_OddDualWeyl_Low_hw_mem
import Theorems.Thm_PI_OddDualWeyl_Low_pw_one
import Theorems.Thm_PI_OddDualWeyl_Low_step

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
open PI PI.OddDualWeyl PI.OddDualWeyl.Low
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.Low
theorem _root_.solution {n : ℕ} (ν : Fin (n + 1) → ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    pw R σ ν ∈ weyl R (n + 1) (n + 1) le_rfl ν := by
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  refine Submonoid.closure_induction_right
    (motive := fun x _ => pw R x ν ∈ weyl R (n + 1) (n + 1) le_rfl ν) ?_ ?_ hσ
  · rw [pw_one]; exact hw_mem _ _
  · intro x _ y hy ih
    obtain ⟨i, rfl⟩ := hy
    obtain ⟨c, hc⟩ := step (R := R) x i ν
    rw [hc]
    exact Submodule.smul_mem _ c (rowDiv_mem _ _ _ _ _ ih)
end PI.OddDualWeyl.Low
