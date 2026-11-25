-- Prove2me | solution 1 for PI.WAU.kg_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:05:44.611701+00:00
-- url     : https://prove2.me/submissions/f493c4f3-b63e-42b8-a370-a0d830b57cfe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionD
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
open PI PI.WAU
open Formalism.MainNotions.S MeasureTheory Matrix Pointwise
namespace PI.WAU
theorem _root_.solution (I : AutInst) : I.Kg 1 = I.Kset := by
  ext x
  refine ⟨fun h => h.1, fun h => ⟨h, fun y hy => ⟨(I.fmat x - 1) *ᵥ y, ?_, by simp⟩⟩⟩
  have h' : ∀ y, y ∈ I.Lf ↔ I.fmat x *ᵥ y ∈ I.Lf := h
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact I.Lf.sub_mem ((h' y).1 hy) hy
end PI.WAU
