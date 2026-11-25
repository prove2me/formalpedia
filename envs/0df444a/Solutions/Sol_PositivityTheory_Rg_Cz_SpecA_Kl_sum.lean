-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.Kl_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:59:45.047825+00:00
-- url     : https://prove2.me/submissions/4ddf7482-65dc-433e-b4d2-2ffb13bca3bd

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_sum_comm
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
open Formalism.REAL
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SpecA
variable {n : ℕ}
namespace PositivityTheory.Rg.Cz.SpecA
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (A B : Module.End ℂ V) (hAB : Commute A B) (α β : ℂ)
    (hA : Kl A α) (hB : Kl B β) : Kl (A + B) (α + β) := by
  obtain ⟨La, hLa⟩ := hA
  obtain ⟨Lb, hLb⟩ := hB
  refine ⟨La.flatMap fun a => Lb.map (a + ·), ?_⟩
  have hc : ∀ a ∈ ({A, B} : Set (Module.End ℂ V)), ∀ b ∈ ({A, B} : Set (Module.End ℂ V)), a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hAB.eq
    · exact hAB.eq.symm
    · rfl
  letI : CommRing (Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))) := Algebra.adjoinCommRingOfComm ℂ hc
  let a' : Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V)) := ⟨A, Algebra.subset_adjoin (by simp)⟩
  let b' : Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V)) := ⟨B, Algebra.subset_adjoin (by simp)⟩
  have hinj : Function.Injective (Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))).val := Subtype.val_injective
  have hA' : (La.map fun a : ℕ => a' - algebraMap ℂ _ (α + a)).prod = 0 := by
    apply hinj
    rw [map_list_prod, map_zero, List.map_map]
    simpa [Function.comp_def, a'] using hLa
  have hB' : (Lb.map fun b : ℕ => b' - algebraMap ℂ _ (β + b)).prod = 0 := by
    apply hinj
    rw [map_list_prod, map_zero, List.map_map]
    simpa [Function.comp_def, b'] using hLb
  have hs := congrArg (Algebra.adjoin ℂ ({A, B} : Set (Module.End ℂ V))).val (sum_comm a' b' α β La Lb hA' hB')
  rw [map_list_prod, map_zero, List.map_map] at hs
  simpa [Function.comp_def, a', b'] using hs
end PositivityTheory.Rg.Cz.SpecA
