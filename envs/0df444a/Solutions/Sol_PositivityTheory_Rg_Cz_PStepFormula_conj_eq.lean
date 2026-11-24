-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.PStepFormula.conj_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:04.369825+00:00
-- url     : https://prove2.me/submissions/0b978f71-5678-4adc-a285-a4df26f79342

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
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace PositivityTheory.Rg.Cz.PStepFormula
theorem _root_.solution (e : V ≃ₗ[ℂ] W) {T : Module.End ℂ V} {T' : Module.End ℂ W}
    (h : ∀ x, e (T x) = T' (e x)) : e.conjAlgEquiv ℂ T = T' := by
  ext x
  simp [LinearEquiv.conjAlgEquiv_apply, h]
end PositivityTheory.Rg.Cz.PStepFormula
