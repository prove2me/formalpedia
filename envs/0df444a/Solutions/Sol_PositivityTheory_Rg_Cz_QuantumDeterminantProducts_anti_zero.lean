-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.QuantumDeterminantProducts.anti_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:50:49.748542+00:00
-- url     : https://prove2.me/submissions/6da8cf74-d110-4c8d-987f-931d9d3553bd

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PPiQdet
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_sg_swap
import Theorems.Thm_PositivityTheory_Rg_Cz_QuantumDeterminantProducts_anti_apply
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
theorem _root_.solution {g : TV n M (Fin n)} (hg : IsAnti g) {I : Fin n → Fin n} (hI : ¬ Function.Injective I) :
    g I = 0 := by
  simp only [Function.Injective] at hI
  push_neg at hI
  obtain ⟨i, j, hij, hne⟩ := hI
  have hIs : I ∘ Equiv.swap i j = I := by
    funext k
    simp only [Function.comp_apply]
    rcases eq_or_ne k i with rfl | hki
    · simp [Equiv.swap_apply_left, hij]
    rcases eq_or_ne k j with rfl | hkj
    · simp [Equiv.swap_apply_right, hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := anti_apply hg (Equiv.swap i j) I
  rw [hIs, sg_swap hne] at h
  have h2 : (2 : ℂ) • g I = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
end PositivityTheory.Rg.Cz.QuantumDeterminantProducts
