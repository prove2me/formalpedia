-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefA_toSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:31.74402+00:00
-- url     : https://prove2.me/submissions/18fdcdd6-cfcb-48c0-869e-80eb5e98737f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefA_inner_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefA_decompM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
section Spec
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
end Spec
section Rep
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
private theorem exists_mem_inner_eq_functional_of_finiteDim {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
    (L : Submodule ℂ Z) [FiniteDimensional ℂ L] (ψ : Z →ₗ[ℂ] ℂ) :
    ∃ f ∈ L, ∀ w ∈ L, inner ℂ f w = ψ w := by
  haveI : CompleteSpace L := FiniteDimensional.complete ℂ L
  refine ⟨(((InnerProductSpace.toDual ℂ L).symm
      (LinearMap.toContinuousLinearMap (ψ.comp L.subtype)) : L) : Z), Submodule.coe_mem _,
      fun w hw => ?_⟩
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := L) (x := ⟨w, hw⟩)
    (y := LinearMap.toContinuousLinearMap (ψ.comp L.subtype))
  rw [Submodule.coe_inner] at h
  simpa using h
private theorem inner_span_eq_zero_of_eigenvalue_gt {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {s : Set X} {C : ℝ} (hs : ∀ u ∈ s, ∃ α : ℝ, α ≤ C ∧ T u = (α : ℂ) • u) {v : X} {β : ℝ}
    (hv : T v = (β : ℂ) • v) (hβ : C < β) : ∀ w ∈ Submodule.span ℂ s, inner ℂ w v = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, hx'⟩ := hs x hx
    exact coefA_inner_eq_zero hT hx' hv (ne_of_lt (lt_of_le_of_lt hα hβ))
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
end Rep
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {T : X →ₗ[ℂ] X} (hT : ∀ x y, inner ℂ (T x) y = inner ℂ x (T y))
    {M' : Submodule ℂ X} (hloc : CoefLocFin T M') (ℓ : X →ₗ[ℂ] ℂ) (C : ℝ)
    {Z₀ : Submodule ℂ X} (hZ₀ : FiniteDimensional ℂ Z₀) (hZM : Z₀ ≤ M')
    (hlow : ∀ y ∈ M', ∀ θ : ℝ, θ ≤ C → T y = (θ : ℂ) • y → y ∈ Z₀)
    (hhigh : ∀ y ∈ M', ∀ θ : ℝ, C < θ → T y = (θ : ℂ) • y → ℓ y = 0) :
    ∃ z ∈ M', ∀ y ∈ M', inner ℂ z y = ℓ y := by
  classical
  have hLZ : Submodule.span ℂ {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y} ≤ Z₀ :=
    Submodule.span_le.mpr (fun y ⟨hyM, θ, hθ, hTy⟩ => hlow y hyM θ hθ hTy)
  haveI := hZ₀
  haveI : FiniteDimensional ℂ
      (Submodule.span ℂ {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y}) :=
    Submodule.finiteDimensional_of_le hLZ
  obtain ⟨z, hzL, hz⟩ := exists_mem_inner_eq_functional_of_finiteDim
    (Submodule.span ℂ {y | y ∈ M' ∧ ∃ θ : ℝ, θ ≤ C ∧ T y = (θ : ℂ) • y}) ℓ
  refine ⟨z, hZM (hLZ hzL), fun y hy => ?_⟩
  obtain ⟨m, b, θ, hsum, hb⟩ := coefA_decompM hT hloc hy
  rw [hsum, inner_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hθ : θ i ≤ C
  · exact hz (b i) (Submodule.subset_span ⟨(hb i).1, θ i, hθ, (hb i).2⟩)
  · push_neg at hθ
    rw [hhigh (b i) (hb i).1 (θ i) hθ (hb i).2]
    exact inner_span_eq_zero_of_eigenvalue_gt hT (fun u hu => hu.2) (hb i).2 hθ z hzL
end ReciprocityTheory.ChartRestriction.DS
