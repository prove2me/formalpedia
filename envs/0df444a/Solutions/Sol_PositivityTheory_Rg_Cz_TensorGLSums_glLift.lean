-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TensorGLSums.glLift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:23.945498+00:00
-- url     : https://prove2.me/submissions/882cf100-e1ff-40e4-b7e7-49a5d3651c53

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGl
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
omit [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TensorGLSums
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) :
    GlRel (fun a b => (lift (E a b) : Module.End ℂ (TV n M P))) := by
  intro a b c d
  have := congrArg (liftA n M P) (hE a b c d)
  simp only [map_sub, map_mul, apply_ite (liftA n M P), map_zero] at this
  exact this
end PositivityTheory.Rg.Cz.TensorGLSums
