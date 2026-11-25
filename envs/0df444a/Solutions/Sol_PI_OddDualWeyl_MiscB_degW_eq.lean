-- Prove2me | solution 1 for PI.OddDualWeyl.MiscB.degW_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:05:15.221187+00:00
-- url     : https://prove2.me/submissions/24f3b90f-765e-4e0f-ba96-524336f32276

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_DegreeBalance
import Theorems.Thm_PI_OddDualWeyl_MiscB_abel

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
open PI.OddDualWeyl.MiscB
namespace PI.OddDualWeyl.MiscB
theorem _root_.solution {k : ℕ} (ν : Fin k → ℕ) (hν : Antitone ν) : degW ν = ∑ s, ν s := by
  have hf : ∀ s, ext0 ν (s + 1) ≤ ext0 ν s := by
    intro s
    unfold ext0
    split_ifs with h1 h2
    · exact hν (Fin.mk_le_mk.2 (Nat.le_succ s))
    · omega
    · exact Nat.zero_le _
    · exact le_rfl
  have h := abel (ext0 ν) hf k
  have hk : ext0 ν k = 0 := by
    unfold ext0
    simp
  rw [hk, mul_zero, add_zero] at h
  have e1 : ∑ s : Fin k, (s.val + 1) * (ν s - nuNext ν s) =
      ∑ s ∈ Finset.range k, (s + 1) * (ext0 ν s - ext0 ν (s + 1)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => (s + 1) * (ext0 ν s - ext0 ν (s + 1))) k]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [ext0, dif_pos s.2]
    rfl
  have e2 : ∑ s : Fin k, ν s = ∑ s ∈ Finset.range k, ext0 ν s := by
    rw [← Fin.sum_univ_eq_sum_range (fun s => ext0 ν s) k]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [ext0, dif_pos s.2]
  unfold degW
  rw [e1, e2, h]
end PI.OddDualWeyl.MiscB
