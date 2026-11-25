-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QuantumDeterminantProducts.X_eq_T_of_antisymm_below
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:41:22.148164+00:00
-- url     : https://prove2.me/submissions/0f9d27a6-2d94-47c9-82cc-e48417fb9d74

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
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
theorem _root_.solution (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (j : Fin n) (w : TV n M (Fin n))
    (hw : ∀ i, i < j → pm (Equiv.swap i j) w = -w) : X E u j w = T E u j w := by
  have hs : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j), pm (Equiv.swap i j)) w = -(((j : ℕ) : ℂ) • w) := by
    rw [LinearMap.sum_apply]
    rw [Finset.sum_congr rfl (fun i hi => hw i (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_neg_distrib, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio, Nat.cast_smul_eq_nsmul]
  simp only [X, T, xJ, LinearMap.add_apply]
  rw [hs, Module.algebraMap_end_apply, Module.algebraMap_end_apply, sub_smul]
  abel
end PositivityTheory.Rg.Cz.QuantumDeterminantProducts
