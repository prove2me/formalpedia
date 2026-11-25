-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefA_ofSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:46.075354+00:00
-- url     : https://prove2.me/submissions/4c61b481-94bd-4f24-888c-a554c8a920f9

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
private theorem exists_inner_comp_eq_functional_of_injOn {E : Submodule ℂ X} [FiniteDimensional ℂ E] (ι : X →ₗ[ℂ] Y)
    (hinj : ∀ y ∈ E, ι y = 0 → y = 0) (φ : X →ₗ[ℂ] ℂ) :
    ∃ x ∈ E, ∀ y ∈ E, inner ℂ (ι x) (ι y) = φ y := by
  have hker : LinearMap.ker (ι.comp E.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hinj w w.2 hw)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (ι.comp E.subtype) hker
  obtain ⟨f, hfR, hf⟩ := exists_mem_inner_eq_functional_of_finiteDim (LinearMap.range (ι.comp E.subtype))
    ((φ.comp E.subtype).comp g)
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hfR
  refine ⟨x, x.2, fun y hy => ?_⟩
  have h1 := hf (ι y) ⟨⟨y, hy⟩, rfl⟩
  have hgy : g (ι y) = ⟨y, hy⟩ := by
    have h2 := LinearMap.congr_fun hg ⟨y, hy⟩
    simpa using h2
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
  rw [h1, hgy]
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
    {TY : Y →ₗ[ℂ] Y} (hTY : ∀ x y, inner ℂ (TY x) y = inner ℂ x (TY y))
    {M' : Submodule ℂ X} (hloc : CoefLocFin T M') (ι : X →ₗ[ℂ] Y)
    (hιT : ∀ y ∈ M', ι (T y) = TY (ι y)) (hinj : ∀ y ∈ M', ι y = 0 → y = 0)
    (hfin : ∀ θ : ℝ, ∃ Z : Submodule ℂ X, FiniteDimensional ℂ Z ∧
      ∀ y ∈ M', T y = (θ : ℂ) • y → y ∈ Z) :
    ∀ z ∈ M', ∃ f ∈ M'.map ι, ∀ y ∈ M', inner ℂ f (ι y) = inner ℂ z y := by
  classical
  intro z hz
  obtain ⟨m, b, θ, hzs, hb⟩ := coefA_decompM hT hloc hz
  have hx : ∀ k : Fin m, ∃ x : X, x ∈ M' ∧ T x = (θ k : ℂ) • x ∧
      ∀ y ∈ M', T y = (θ k : ℂ) • y → inner ℂ (ι x) (ι y) = inner ℂ (b k) y := by
    intro k
    obtain ⟨Z, hZd, hZ⟩ := hfin (θ k)
    have hmemE : ∀ y, y ∈ M' ⊓ LinearMap.ker (T - (θ k : ℂ) • LinearMap.id) ↔
        y ∈ M' ∧ T y = (θ k : ℂ) • y := by
      intro y
      simp [Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
    have hEZ : M' ⊓ LinearMap.ker (T - (θ k : ℂ) • LinearMap.id) ≤ Z := fun y hy =>
      hZ y ((hmemE y).mp hy).1 ((hmemE y).mp hy).2
    haveI := hZd
    haveI : FiniteDimensional ℂ ↥(M' ⊓ LinearMap.ker (T - (θ k : ℂ) • LinearMap.id)) :=
      Submodule.finiteDimensional_of_le hEZ
    obtain ⟨x, hxE, hxr⟩ := exists_inner_comp_eq_functional_of_injOn ι (fun y hy => hinj y ((hmemE y).mp hy).1)
      (innerₛₗ ℂ (b k))
    refine ⟨x, ((hmemE x).mp hxE).1, ((hmemE x).mp hxE).2, fun y hy hTy => ?_⟩
    rw [hxr y ((hmemE y).mpr ⟨hy, hTy⟩)]
    first
      | rfl
      | simp
  choose x hxM hxT hxr using hx
  refine ⟨ι (∑ k, x k), Submodule.mem_map_of_mem (Submodule.sum_mem _ (fun k _ => hxM k)), ?_⟩
  intro y hy
  obtain ⟨n, c, η, hys, hc⟩ := coefA_decompM hT hloc hy
  rw [map_sum, hzs, hys, sum_inner, sum_inner]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [map_sum, inner_sum, inner_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hkj : θ k = η j
  · exact hxr k (c j) (hc j).1 (by rw [hkj]; exact (hc j).2)
  · have h1 : inner ℂ (b k) (c j) = 0 := coefA_inner_eq_zero hT (hb k).2 (hc j).2 hkj
    have hTYx : TY (ι (x k)) = (θ k : ℂ) • ι (x k) := by
      rw [← hιT _ (hxM k), hxT k, map_smul]
    have hTYc : TY (ι (c j)) = (η j : ℂ) • ι (c j) := by
      rw [← hιT _ (hc j).1, (hc j).2, map_smul]
    rw [h1, coefA_inner_eq_zero hTY hTYx hTYc hkj]
end ReciprocityTheory.ChartRestriction.DS
