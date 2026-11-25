-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QuantumDeterminantProducts.evA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:04.149907+00:00
-- url     : https://prove2.me/submissions/390bcbed-4e7e-41cd-a0f6-adf56ab2ed00

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_T_apply
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
open PositivityTheory.Rg.Cz.QuantumDeterminantProducts
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.QuantumDeterminantProducts
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (h : TV n M (Fin n)) (l : List (Fin n)) (I : Fin n → Fin n) :
    (l.map (T E u)).prod h I = ev E u l I h := by
  induction l generalizing I with
  | nil => rfl
  | cons k l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ev, T_apply, ih]
end PositivityTheory.Rg.Cz.QuantumDeterminantProducts
