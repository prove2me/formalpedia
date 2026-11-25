-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.CtrX.omc_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:31:01.160879+00:00
-- url     : https://prove2.me/submissions/a5e149e2-5f6c-4b92-8f4f-a79d2dbed4f5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PContractE
import Theorems.Thm_PositivityTheory_Rg_Cz_CtrX_omc_glue_j
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.CtrX
open PositivityTheory.Rg.Cz
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
omit [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.CtrX
theorem _root_.solution {m : ℕ} (j : Fin m) (a b : Fin n) (R : {p // p ≠ j} → Fin n) :
    Function.update (omcGlue j b R) j a = omcGlue j a R := by
  funext p
  by_cases hp : p = j
  · subst hp
    simp [omc_glue_j]
  · rw [Function.update_of_ne hp]
    simp [omcGlue, hp]
end PositivityTheory.Rg.Cz.CtrX
