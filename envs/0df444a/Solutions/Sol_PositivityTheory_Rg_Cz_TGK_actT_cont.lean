-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TGK.actT_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:38:37.397846+00:00
-- url     : https://prove2.me/submissions/8e754f9f-1cef-4762-af86-bf3303203593

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_LiftCommEAt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTensorGKB
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.TGK
variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
namespace PositivityTheory.Rg.Cz.TGK
theorem _root_.solution {ι Γ : Type} [TopologicalSpace Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (hκ : ∀ τ i j, Continuous fun γ => κ τ γ i j)
    (hc : ∀ y (lam : M →ₗ[ℂ] ℂ), Continuous fun γ => lam (ρ γ y)) (y : TV n M P) (lam : TV n M P →ₗ[ℂ] ℂ) :
    Continuous fun γ => lam (actT lab κ ρ γ y) := by
  classical
  have h1 : ∀ x : TV n M P, lam x = ∑ I : P → Fin n, (lam ∘ₗ LinearMap.single ℂ (fun _ : P → Fin n => M) I) (x I) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    simp [map_sum]
  have key : (fun γ => lam (actT lab κ ρ γ y)) = fun γ => ∑ I : P → Fin n, ∑ J : P → Fin n,
      (∏ p : P, κ (lab p) γ (I p) (J p)) * (lam ∘ₗ LinearMap.single ℂ (fun _ : P → Fin n => M) I) (ρ γ (y J)) := by
    funext γ
    rw [h1]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [map_smul, map_smul, smul_eq_mul]
  rw [key]
  refine continuous_finset_sum _ fun I _ => continuous_finset_sum _ fun J _ => ?_
  exact (continuous_finset_prod _ fun p _ => hκ _ _ _).mul (hc (y J) _)
end PositivityTheory.Rg.Cz.TGK
