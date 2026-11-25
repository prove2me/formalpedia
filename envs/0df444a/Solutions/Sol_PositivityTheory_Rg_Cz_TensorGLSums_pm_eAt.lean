-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TensorGLSums.pm_eAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:38:26.096207+00:00
-- url     : https://prove2.me/submissions/db669ca4-6995-4a05-974e-14ecaa9a7a4f

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
theorem _root_.solution (σ : Equiv.Perm P) (p : P) (a b : Fin n) :
    (pm σ * eAt p a b : Module.End ℂ (TV n M P)) = eAt (σ p) a b * pm σ := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, eAt_apply, pm_apply, Function.comp_apply]
  rw [Function.update_comp_equiv]
  simp
end PositivityTheory.Rg.Cz.TensorGLSums
