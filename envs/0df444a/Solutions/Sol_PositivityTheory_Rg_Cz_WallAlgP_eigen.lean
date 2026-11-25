-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.WallAlgP.eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:07.74699+00:00
-- url     : https://prove2.me/submissions/c989fa86-e1c6-438f-bada-3529762f1638

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PWallAlgA
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
open PositivityTheory.Rg.Cz.WallAlgP
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.WallAlgP
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (Y : Submodule ℂ V) (T : Module.End ℂ V)
    (hT : ∀ y ∈ Y, T y ∈ Y) (μ : ℕ → ℂ) (L : List ℕ) (hL : (L.map fun r => T - algebraMap ℂ _ (μ r)).prod = 0)
    (y : V) (hy : y ∈ Y) (hy0 : y ≠ 0) : ∃ z ∈ Y, z ≠ 0 ∧ ∃ r : ℕ, T z = μ r • z := by
  have pres : ∀ (L : List ℕ), ∀ y ∈ Y, (L.map fun r => T - algebraMap ℂ _ (μ r)).prod y ∈ Y := by
    intro L
    induction L with
    | nil => intro y hy; simpa using hy
    | cons r L ih =>
      intro y hy
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply,
        Module.algebraMap_end_apply]
      exact Y.sub_mem (hT _ (ih y hy)) (Y.smul_mem _ (ih y hy))
  have main : ∀ (L : List ℕ), (L.map fun r => T - algebraMap ℂ _ (μ r)).prod y = 0 →
      ∃ z ∈ Y, z ≠ 0 ∧ ∃ r : ℕ, T z = μ r • z := by
    intro L
    induction L with
    | nil => intro h; simp at h; exact absurd h hy0
    | cons r L ih =>
      intro h
      by_cases hz : (L.map fun r => T - algebraMap ℂ _ (μ r)).prod y = 0
      · exact ih hz
      · refine ⟨_, pres L y hy, hz, r, ?_⟩
        simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply,
          Module.algebraMap_end_apply] at h
        exact sub_eq_zero.mp h
  exact main L (by rw [hL]; rfl)
end PositivityTheory.Rg.Cz.WallAlgP
