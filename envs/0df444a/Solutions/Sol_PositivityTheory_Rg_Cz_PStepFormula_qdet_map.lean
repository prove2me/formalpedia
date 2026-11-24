-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.qdet_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:25.461208+00:00
-- url     : https://prove2.me/submissions/f419c05f-3d8f-4522-b5e6-0ccfd32f58b4

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
theorem _root_.solution {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (E : Fin n → Fin n → A) (u : ℂ) : f (qdet E u) = qdet (fun a b => f (E a b)) u := by
  simp only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Function.comp_def, Tm,
    map_add, apply_ite f, AlgHom.commutes, map_zero]
end PositivityTheory.Rg.Cz.PStepFormula
