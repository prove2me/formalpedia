-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.lift_PiJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:00.662724+00:00
-- url     : https://prove2.me/submissions/e003363d-cc1b-4259-9b0b-1785a98eeec9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_liftA_apply
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
theorem _root_.solution {m : ℕ} {P : Type} (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) :
    (lift (PiJ m E u) : Module.End ℂ (TV n (TV n M (Fin m)) P)) =
      (List.ofFn fun i => algebraMap ℂ _ u + lift (xJ E i)).prod := by
  rw [← liftA_apply]
  simp only [PiJ, map_list_prod, List.map_ofFn, Function.comp_def, map_add, AlgHom.commutes, liftA_apply]
end PositivityTheory.Rg.Cz.PStepFormula
