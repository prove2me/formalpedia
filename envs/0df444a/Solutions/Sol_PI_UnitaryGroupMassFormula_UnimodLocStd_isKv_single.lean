-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isKv_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:43.341931+00:00
-- url     : https://prove2.me/submissions/ad544f2f-997a-4161-9127-d6cbf04f384a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {w : ℂ} (hw : IsK b d (w / lam)) (i : m) : IsKv b d lam (Pi.single i w) := by
  intro j
  rw [Pi.single_apply]
  split_ifs
  · exact hw
  · rw [zero_div]
    exact ⟨0, 0, 1, one_ne_zero, by simp⟩
end PI.UnitaryGroupMassFormula.UnimodLocStd
