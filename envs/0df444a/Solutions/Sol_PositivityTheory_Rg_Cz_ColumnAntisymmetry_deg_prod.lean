-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ColumnAntisymmetry.deg_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:00.925604+00:00
-- url     : https://prove2.me/submissions/dfaf2029-2bc7-4e36-919e-188258efbdfa

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PColAntiA
import Theorems.Thm_PositivityTheory_Rg_Cz_ColumnAntisymmetry_deg_mul
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
open PositivityTheory.Rg.Cz.ColumnAntisymmetry
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
variable {m : ℕ} {E : Fin n → Fin n → Module.End ℂ M}
namespace PositivityTheory.Rg.Cz.ColumnAntisymmetry
theorem _root_.solution : ∀ (k : ℕ) (f : Fin k → Module.End ℂ (TV n M (Fin m))) (e : Fin k → ℕ),
    (∀ i, Deg E (e i) (f i)) → Deg E (∑ i, e i) (List.ofFn f).prod := by
  intro k
  induction k with
  | zero => intro f e _; simpa using Deg.one (E := E) (P := Fin m) 0
  | succ k ih =>
    intro f e hf
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact deg_mul (hf 0) (ih _ _ fun i => hf i.succ)
end PositivityTheory.Rg.Cz.ColumnAntisymmetry
