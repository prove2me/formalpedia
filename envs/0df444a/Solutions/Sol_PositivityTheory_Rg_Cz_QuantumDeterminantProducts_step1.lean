-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QuantumDeterminantProducts.step1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:49:29.175994+00:00
-- url     : https://prove2.me/submissions/3dbcc5c5-e835-4e8c-99de-135899ee90c0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_sg_swap
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_X_eq_T_of_antisymm_below
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_T_comm
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
theorem _root_.solution (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (u : ℂ) (g : TV n M (Fin n))
    (hg : IsAnti g) (l : List (Fin n)) (hl : l.Pairwise (· < ·)) :
    (l.map (X E u)).prod g = (l.map (T E u)).prod g := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.pairwise_cons] at hl
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [ih hl.2]
    apply X_eq_T_of_antisymm_below
    intro i hi
    have hc : Commute (pm (Equiv.swap i k)) (l.map (T E u)).prod := by
      apply Commute.list_prod_right
      intro b hb
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      have hkj := hl.1 j hj
      apply T_comm hT E hE u
      apply Equiv.swap_apply_of_ne_of_ne
      · exact ne_of_gt (lt_trans hi hkj)
      · exact ne_of_gt hkj
    rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
    rw [hg (Equiv.swap i k), sg_swap (ne_of_lt hi)]
    simp
end PositivityTheory.Rg.Cz.QuantumDeterminantProducts
