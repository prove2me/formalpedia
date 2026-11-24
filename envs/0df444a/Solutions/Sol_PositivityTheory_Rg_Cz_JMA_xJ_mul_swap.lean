-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.JMA.xJ_mul_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:26.274329+00:00
-- url     : https://prove2.me/submissions/27fcc65e-3c2c-4f45-988c-acb390ea1e21

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PJmComm
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_pm_swap_sq
import Theorems.Thm_PositivityTheory_Rg_Cz_JMA_xJ_succ
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
open PositivityTheory.Rg.Cz.JMA
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.JMA
theorem _root_.solution (hT : TensorGl) {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E) {m : ℕ} (i j : Fin m)
    (hij : (i : ℕ) + 1 = j) : xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 := by
  rw [xJ_succ hT hE i j hij]
  simp only [add_mul, mul_assoc, pm_swap_sq, mul_one]
end PositivityTheory.Rg.Cz.JMA
