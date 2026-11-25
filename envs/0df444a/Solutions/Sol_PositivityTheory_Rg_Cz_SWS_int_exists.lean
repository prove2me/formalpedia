-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.SWS.int_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:34:56.270074+00:00
-- url     : https://prove2.me/submissions/733dbb39-e544-423e-9de4-d6d1eff444f6

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStartB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PSWStart
import Theorems.Thm_PositivityTheory_Rg_Cz_SWS_integrable_of_cont
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
theorem _root_.solution (ρ : Γ → Module.End ℂ M) (y : M)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ y)))
    (hcont : ∀ lam : M →ₗ[ℂ] ℂ, Continuous fun γ => lam (ρ γ y)) {g : Γ → ℂ} (hg : Continuous g) :
    ∃ x : M, ∀ lam : M →ₗ[ℂ] ℂ, lam x = ∫ k, g k * lam (ρ k y) ∂μ := by
  classical
  haveI := hfin
  set V := Submodule.span ℂ (Set.range fun γ => ρ γ y) with hV
  let b := Module.finBasis ℂ V
  have hext : ∀ i, ∃ f : M →ₗ[ℂ] ℂ, f ∘ₗ V.subtype = b.coord i := fun i => LinearMap.exists_extend _
  choose e he using hext
  have hmem : ∀ k, ρ k y ∈ V := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hrepr : ∀ k, ρ k y = ∑ i, e i (ρ k y) • (b i : M) := by
    intro k
    have hc : ∀ i, e i (ρ k y) = b.repr ⟨ρ k y, hmem k⟩ i := fun i => by
      have := LinearMap.congr_fun (he i) ⟨ρ k y, hmem k⟩
      simpa using this
    simp_rw [hc]
    have h := congrArg Subtype.val (b.sum_repr ⟨ρ k y, hmem k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  have hint : ∀ i, Integrable (fun k => g k * e i (ρ k y)) μ := fun i =>
    integrable_of_cont μ (hg.mul (hcont (e i)))
  refine ⟨∑ i, (∫ k, g k * e i (ρ k y) ∂μ) • (b i : M), fun lam => ?_⟩
  have hpt : ∀ k, g k * lam (ρ k y) = ∑ i, g k * e i (ρ k y) * lam (b i) := by
    intro k
    conv_lhs => rw [hrepr k]
    simp [map_sum, Finset.mul_sum, mul_assoc]
  simp_rw [hpt]
  rw [integral_finset_sum _ (fun i _ => (hint i).mul_const _)]
  simp only [map_sum, map_smul, smul_eq_mul, integral_mul_const]
end PositivityTheory.Rg.Cz.SWS
