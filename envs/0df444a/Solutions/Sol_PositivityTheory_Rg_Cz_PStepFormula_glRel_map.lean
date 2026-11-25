-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.glRel_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:36:29.732684+00:00
-- url     : https://prove2.me/submissions/7d15e90f-e510-4f32-a81b-307907974160

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
namespace PositivityTheory.Rg.Cz.PStepFormula
theorem _root_.solution {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    {E : Fin n → Fin n → A} (h : GlRel E) : GlRel (fun a b => f (E a b)) := by
  intro a b c d
  have := congrArg f (h a b c d)
  simpa only [map_sub, map_mul, apply_ite f, map_zero] using this
end PositivityTheory.Rg.Cz.PStepFormula
