-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TensorGLSums.eAt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:22.374012+00:00
-- url     : https://prove2.me/submissions/4615ebad-aad3-422c-87f3-bef1491b378a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGl
import Theorems.Thm_PositivityTheory_Rg_Cz_eAt_apply
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
open PositivityTheory.Rg.Cz.TensorGLSums
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TensorGLSums
theorem _root_.solution (p : P) (a b c d : Fin n) :
    (eAt p a b * eAt p c d : Module.End ℂ (TV n M P)) = if b = c then eAt p a d else 0 := by
  refine LinearMap.ext fun f => funext fun I => ?_
  by_cases hbc : b = c
  · subst hbc
    simp [Module.End.mul_apply, eAt_apply, Function.update_idem]
  · simp [Module.End.mul_apply, eAt_apply, hbc]
end PositivityTheory.Rg.Cz.TensorGLSums
