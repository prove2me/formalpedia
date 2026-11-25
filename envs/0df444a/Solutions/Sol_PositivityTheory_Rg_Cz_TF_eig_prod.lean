-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TF.eig_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:37:00.396674+00:00
-- url     : https://prove2.me/submissions/af751a37-096f-4414-877a-345e0172fd5a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
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
open PositivityTheory.Rg.Cz.TF
namespace PositivityTheory.Rg.Cz.TF
theorem _root_.solution {W : Type*} [AddCommGroup W] [Module ℂ W] (φ : W →ₗ[ℂ] ℂ) :
    ∀ l : List (Module.End ℂ W), (∀ a ∈ l, ∃ μ : ℂ, μ ≠ 0 ∧ φ ∘ₗ a = μ • φ) →
      ∃ μ : ℂ, μ ≠ 0 ∧ φ ∘ₗ l.prod = μ • φ := by
  intro l hl
  induction l with
  | nil => exact ⟨1, one_ne_zero, by ext; simp⟩
  | cons a l ih =>
    obtain ⟨μa, hμa, ha⟩ := hl a (by simp)
    obtain ⟨μl, hμl, hl1⟩ := ih (fun b hb => hl b (List.mem_cons_of_mem _ hb))
    refine ⟨μa * μl, mul_ne_zero hμa hμl, LinearMap.ext fun w => ?_⟩
    have e1 := LinearMap.congr_fun ha (l.prod w)
    have e2 := LinearMap.congr_fun hl1 w
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at e1 e2 ⊢
    rw [List.prod_cons, Module.End.mul_apply, e1, e2, mul_assoc]
end PositivityTheory.Rg.Cz.TF
