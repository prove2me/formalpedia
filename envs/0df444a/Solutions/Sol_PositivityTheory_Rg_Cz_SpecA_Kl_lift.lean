-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SpecA.Kl_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:26.815653+00:00
-- url     : https://prove2.me/submissions/a1a14fff-493b-48fb-98bd-4145ff2985dd

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
theorem _root_.solution {V P : Type} [AddCommGroup V] [Module ℂ V] (X : Module.End ℂ V) (s : ℂ) (h : Kl X s) :
    Kl (lift X : Module.End ℂ (TV n V P)) s := by
  obtain ⟨L, hL⟩ := h
  refine ⟨L, ?_⟩
  refine LinearMap.ext fun f => funext fun I => ?_
  have hc : (LinearMap.proj I : TV n V P →ₗ[ℂ] V) ∘ₗ lift X = X ∘ₗ LinearMap.proj I :=
    LinearMap.ext fun f => rfl
  have hP := prodL_nat (LinearMap.proj I) (lift X) X hc (fun r : ℕ => s + (r : ℂ)) L
  rw [hL, LinearMap.zero_comp] at hP
  simpa using LinearMap.congr_fun hP f
end PositivityTheory.Rg.Cz.SpecA
