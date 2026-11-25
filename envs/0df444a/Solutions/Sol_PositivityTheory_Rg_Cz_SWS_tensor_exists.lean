-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SWS.tensor_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:18.829353+00:00
-- url     : https://prove2.me/submissions/db2c0930-92ce-4ff9-afb3-92ef7195d38b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStart
import Theorems.Thm_PositivityTheory_Rg_Cz_SWS_int_exists
import Theorems.Thm_PositivityTheory_Rg_Cz_SWS_mono_left
import Theorems.Thm_PositivityTheory_Rg_Cz_SWS_integrable_of_cont
import Theorems.Thm_PositivityTheory_Rg_Cz_SWS_mono_cont
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
open Formalism.REAL Matrix MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.SWS
variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
  {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}
variable [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : Measure Γ) [IsFiniteMeasure μ]
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.Rg.Cz.SWS
theorem _root_.solution [IsTopologicalGroup Γ] [μ.IsMulLeftInvariant] {E : ι → Fin n → Fin n → Module.End ℂ M}
    {ρ : Γ → Module.End ℂ M} (hK : IsKD bar κ) (hG : IsGK bar κ E ρ) (y : M) {m : ℕ} (lab : Fin m → ι)
    (c : ι → ℤ) (K : Fin m → Fin n) :
    ∃ ξ : TV n M (Fin m), (∀ γ, actT lab κ ρ γ ξ = (∏ τ, (κ τ γ).det ^ (-c τ)) • ξ) ∧
      ∀ I (lam : M →ₗ[ℂ] ℂ), lam (ξ I) = ∫ k, mono κ lab c I K k * lam (ρ k y) ∂μ := by
  classical
  choose ξ hξ using fun I : Fin m → Fin n =>
    int_exists μ ρ y (hG.fin y) (hG.cont y) (g := mono κ lab c I K) (mono_cont hK lab c I K)
  refine ⟨ξ, fun γ => ?_, hξ⟩
  have hLc : ∀ lam : M →ₗ[ℂ] ℂ, Continuous fun k => lam (ρ (γ * k) y) := by
    intro lam
    simpa [hG.mul, Module.End.mul_apply] using hG.cont y (lam ∘ₗ ρ γ)
  have hD : (∏ τ, (κ τ γ).det ^ (-c τ)) = (∏ τ, (κ τ γ).det ^ (c τ))⁻¹ := by
    simp [_root_.zpow_neg, Finset.prod_inv_distrib]
  funext I
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro lam
  rw [map_sub, sub_eq_zero]
  have h1 : ∀ J, lam (ρ γ (ξ J)) = ∫ k, mono κ lab c J K k * lam (ρ (γ * k) y) ∂μ := by
    intro J
    have := hξ J (lam ∘ₗ ρ γ)
    simpa [hG.mul, Module.End.mul_apply] using this
  simp [actT, h1, hξ I lam]
  simp_rw [← integral_const_mul]
  rw [← integral_finset_sum]
  · rw [← integral_mul_left_eq_self
      (fun x => (∏ τ, (κ τ γ).det ^ (c τ))⁻¹ * (mono κ lab c I K x * lam (ρ x y))) γ]
    congr 1
    funext k
    rw [← mul_assoc, ← hD, ← mono_left hK lab c I K γ k, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro J _
    ring
  · intro J _
    exact integrable_of_cont μ (continuous_const.mul ((mono_cont hK lab c J K).mul (hLc lam)))
end PositivityTheory.Rg.Cz.SWS
