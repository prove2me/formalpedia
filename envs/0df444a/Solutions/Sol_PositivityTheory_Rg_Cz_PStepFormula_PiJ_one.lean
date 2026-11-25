-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.PiJ_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:59.555208+00:00
-- url     : https://prove2.me/submissions/a4cceb75-cdbf-491c-a314-06ed36e8cebe

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.PStepFormula
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.PStepFormula
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) :
    (PiJ 1 E u : Module.End ℂ (TV n M (Fin 1))) = algebraMap ℂ _ u + Om E 0 := by
  have : (Finset.univ.filter fun i : Fin 1 => i < 0) = ∅ := by
    ext i; simp
  simp [PiJ, xJ]
end PositivityTheory.Rg.Cz.PStepFormula
