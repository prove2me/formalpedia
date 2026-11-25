-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.Kl_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:31.274749+00:00
-- url     : https://prove2.me/submissions/e1acad97-e10b-4547-abc6-0178925014b2

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSpectrum
import Theorems.Thm_PositivityTheory_Rg_Cz_SpecA_prodL_nat
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
theorem _root_.solution {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (Φ : V →ₗ[ℂ] W) (hΦ : Function.Injective Φ) (A : Module.End ℂ V) (B : Module.End ℂ W) (h : Φ ∘ₗ A = B ∘ₗ Φ)
    (s : ℂ) (hB : Kl B s) : Kl A s := by
  obtain ⟨L, hL⟩ := hB
  refine ⟨L, ?_⟩
  have hP := prodL_nat Φ A B h (fun r : ℕ => s + (r : ℂ)) L
  rw [hL, LinearMap.zero_comp] at hP
  ext v
  apply hΦ
  rw [LinearMap.zero_apply, map_zero]
  simpa using LinearMap.congr_fun hP v
end PositivityTheory.Rg.Cz.SpecA
