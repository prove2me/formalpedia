-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.ofFn_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:33:03.225491+00:00
-- url     : https://prove2.me/submissions/9d4d962a-5d46-4eaa-b82f-c47a1d936fcd

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
theorem _root_.solution (f : V →ₗ[ℂ] W) {t : ℕ} (A : Fin t → Module.End ℂ V) (B : Fin t → Module.End ℂ W)
    (h : ∀ k, f ∘ₗ A k = B k ∘ₗ f) : f ∘ₗ (List.ofFn A).prod = (List.ofFn B).prod ∘ₗ f := by
  induction t with
  | zero => refine LinearMap.ext fun v => ?_; simp
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h 0, LinearMap.comp_assoc,
      ih (fun k => A k.succ) (fun k => B k.succ) (fun k => h _), LinearMap.comp_assoc]
end PositivityTheory.Rg.Cz.ChainP
