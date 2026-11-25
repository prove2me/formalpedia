-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.xJ_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:43:10.629968+00:00
-- url     : https://prove2.me/submissions/7a27e4dc-fd4f-4a30-ad2b-77d5af4f7a08

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_xJ_apply
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
theorem _root_.solution {m : ℕ} {M₁ M₂ : Type} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    (E₁ : Fin n → Fin n → Module.End ℂ M₁) (E₂ : Fin n → Fin n → Module.End ℂ M₂) (φ : M₁ →ₗ[ℂ] M₂)
    (h : ∀ a b, φ ∘ₗ E₁ a b = E₂ a b ∘ₗ φ) (j : Fin m) :
    LinearMap.compLeft φ (Fin m → Fin n) ∘ₗ xJ E₁ j = xJ E₂ j ∘ₗ LinearMap.compLeft φ (Fin m → Fin n) := by
  have h' : ∀ a b v, φ (E₁ a b v) = E₂ a b (φ v) := fun a b v => LinearMap.congr_fun (h a b) v
  refine LinearMap.ext fun f => funext fun I => ?_
  simp [xJ_apply, map_add, map_sum, h', LinearMap.compLeft_apply]
end PositivityTheory.Rg.Cz.SpecA
