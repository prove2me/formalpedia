-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.prodL_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:30.553577+00:00
-- url     : https://prove2.me/submissions/e8ffd96e-648c-4dec-b1e2-de0f5d39d7e4

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
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
theorem _root_.solution {ι V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : V →ₗ[ℂ] W) (A : Module.End ℂ V) (B : Module.End ℂ W) (h : Φ ∘ₗ A = B ∘ₗ Φ) (g : ι → ℂ) (L : List ι) :
    Φ ∘ₗ (L.map fun r => A - algebraMap ℂ _ (g r)).prod = (L.map fun r => B - algebraMap ℂ _ (g r)).prod ∘ₗ Φ := by
  induction L with
  | nil =>
    ext v
    simp
  | cons r L ih =>
    have key : Φ ∘ₗ (A - algebraMap ℂ _ (g r)) = (B - algebraMap ℂ _ (g r)) ∘ₗ Φ := by
      ext v
      have hv := LinearMap.congr_fun h v
      simp only [LinearMap.comp_apply] at hv
      simp [hv]
    simp only [List.map_cons, List.prod_cons]
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, key,
      LinearMap.comp_assoc, ih, LinearMap.comp_assoc]
end PositivityTheory.Rg.Cz.SpecA
