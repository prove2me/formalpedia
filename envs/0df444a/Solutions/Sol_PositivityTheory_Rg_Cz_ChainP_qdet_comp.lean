-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.ChainP.qdet_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:48.770007+00:00
-- url     : https://prove2.me/submissions/59036ddc-3586-4c4c-bfd3-d5bb1e544bea

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PChainA
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_intCast_comp
import Theorems.Thm_PositivityTheory_Rg_Cz_ChainP_ofFn_comp
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
theorem _root_.solution {n : ℕ} (f : V →ₗ[ℂ] W) (E : Fin n → Fin n → Module.End ℂ V)
    (F : Fin n → Fin n → Module.End ℂ W) (h : ∀ a b, f ∘ₗ E a b = F a b ∘ₗ f) (u : ℂ) :
    f ∘ₗ qdet E u = qdet F u ∘ₗ f := by
  unfold qdet qminor
  have key : ∀ σ : Equiv.Perm (Fin n), f ∘ₗ (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ V) *
      (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod) =
      (((Equiv.Perm.sign σ : ℤ) : Module.End ℂ W) *
      (List.ofFn fun k : Fin n => Tm F (u - (k : ℂ)) (id (σ k)) (id k)).prod) ∘ₗ f := fun σ => by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, intCast_comp,
    LinearMap.comp_assoc, ofFn_comp f _ _ (fun k => ?_), LinearMap.comp_assoc]
    simp only [Tm]
    rw [LinearMap.comp_add, LinearMap.add_comp, h]
    congr 1
    split_ifs
    · refine LinearMap.ext fun v => ?_; simp
    · simp
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun σ _ => LinearMap.congr_fun (key σ) v
end PositivityTheory.Rg.Cz.ChainP
