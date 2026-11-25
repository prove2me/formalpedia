-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.listSub_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:32:45.918056+00:00
-- url     : https://prove2.me/submissions/e5769973-93d9-4769-868c-57df6ccfe034

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
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
open PositivityTheory.Rg.Cz.ChainP
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
namespace PositivityTheory.Rg.Cz.ChainP
theorem _root_.solution (f : V →ₗ[ℂ] W) (A : Module.End ℂ V) (B : Module.End ℂ W) (h : f ∘ₗ A = B ∘ₗ f)
    (L : List ℂ) :
    f ∘ₗ (L.map fun r => A - algebraMap ℂ _ r).prod = (L.map fun r => B - algebraMap ℂ _ r).prod ∘ₗ f := by
  have key : ∀ r : ℂ, f ∘ₗ (A - algebraMap ℂ _ r) = (B - algebraMap ℂ _ r) ∘ₗ f := by
    intro r
    ext v
    have hv := LinearMap.congr_fun h v
    simp only [LinearMap.comp_apply] at hv
    simp [hv]
  induction L with
  | nil =>
    ext v
    simp
  | cons r L ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, key r,
      LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc]
end PositivityTheory.Rg.Cz.ChainP
