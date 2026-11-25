-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.rv_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:40:07.162091+00:00
-- url     : https://prove2.me/submissions/4fa97451-5086-4d9b-aac3-56ed30712052

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_HJMulVecGen
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_rv_hJ
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable (I : Formalism.MainNotions.S.AutInst)
variable {I}
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {r : ℕ} {e f : Fin r → Fin I.n → I.E} {z : Fin I.n → I.E} (hF : IsFrame I e f z)
    (v : NumberField.InfinitePlace I.F) :
    (∀ a b, hJ (I.ε v) (rv I v (e a)) (rv I v (e b)) = 0) ∧
    (∀ a b, hJ (I.ε v) (rv I v (f a)) (rv I v (f b)) = 0) ∧
    (∀ a b, hJ (I.ε v) (rv I v (e a)) (rv I v (f b)) = if a = b then 1 else 0) ∧
    (∀ a, hJ (I.ε v) (rv I v (e a)) (rv I v z) = 0 ∧ hJ (I.ε v) (rv I v (f a)) (rv I v z) = 0) ∧
    hJ (I.ε v) (rv I v z) (rv I v z) ≠ 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hF
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ?_, ?_⟩
  · rw [rv_hJ, h1, map_zero]
  · rw [rv_hJ, h2, map_zero]
  · rw [rv_hJ, h3]
    split_ifs <;> simp
  · rw [rv_hJ, rv_hJ, (h4 a).1, (h4 a).2, map_zero]
    exact ⟨rfl, rfl⟩
  · rw [rv_hJ]
    exact (map_ne_zero _).mpr h5
end PI.ScMuExists.UnitaryGroupMassFormula
