-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.curF_Om_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:27.329803+00:00
-- url     : https://prove2.me/submissions/e5084a6d-e57b-43dd-b809-b23d92d74e83

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PStepFormulaA
import Theorems.Thm_PositivityTheory_Rg_Cz_PStepFormula_app_upd_l
import Theorems.Thm_PositivityTheory_Rg_Cz_Om_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_curF_apply
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
theorem _root_.solution {m k : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (i : Fin m) (f : TV n M (Fin (m + k))) :
    curF n M m k (Om E (Fin.castAdd k i) f) = lift (Om E i) (curF n M m k f) := by
  funext J I
  simp only [curF_apply, Om_apply, Fin.append_left, app_upd_l, lift_apply]
end PositivityTheory.Rg.Cz.PStepFormula
