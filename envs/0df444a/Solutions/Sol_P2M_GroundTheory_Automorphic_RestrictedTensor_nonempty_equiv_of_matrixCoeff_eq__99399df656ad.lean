-- Prove2me | solution 1 for P2M_GroundTheory_Automorphic_RestrictedTensor_nonempty_equiv_of_matrixCoeff_eq__99399df656ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:50.857462+00:00
-- url     : https://prove2.me/submissions/3b8cb78d-f6bb-4eab-9c0e-5a9c283cd31d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mem_span_mOrbit
import Theorems.Thm_P2M_GroundTheory_Automorphic_RestrictedTensor_eq_zero_of_forall_apply__260edcdff289
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mOrbitMap_single
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_mOrbitMap_mapDomain
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_linearForm_mOrbitMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {M : Type*} [Monoid M] {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {ρ : Representation ℂ M V} {σ : Representation ℂ M W}
    [ρ.IsIrreducible] [σ.IsIrreducible] {v : V} {l : Dual ℂ V} {w : W} {m : Dual ℂ W}
    (h : ∀ g, l (ρ g v) = m (σ g w)) (hne : ∃ g, l (ρ g v) ≠ 0) : Nonempty (ρ.Equiv σ) := by
  obtain ⟨g₀, hg₀⟩ := hne
  have hv : v ≠ 0 := by rintro rfl; simp at hg₀
  have hm : m ≠ 0 := by rintro rfl; exact hg₀ (by rw [h]; rfl)
  have hker : LinearMap.ker (mOrbitMap ρ v) ≤ LinearMap.ker (mOrbitMap σ w) := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    by_contra hne
    apply hm
    refine eq_zero_of_forall_apply' (ρ := σ) hne fun k => ?_
    rw [linearForm_mOrbitMap]
    have := linearForm_mOrbitMap ρ v l k c
    rw [hc, map_zero, map_zero] at this
    rw [this]
    exact Finsupp.sum_congr fun g _ => by rw [h]
  have hsurj : Function.Surjective (mOrbitMap ρ v) := by
    intro x
    have hx := mem_span_mOrbit (ρ := ρ) hv x
    rw [← Finsupp.range_linearCombination] at hx
    exact hx
  let e := LinearMap.quotKerEquivOfSurjective (mOrbitMap ρ v) hsurj
  let F : V →ₗ[ℂ] W := ((LinearMap.ker (mOrbitMap ρ v)).liftQ (mOrbitMap σ w) hker).comp
    e.symm.toLinearMap
  have hF : ∀ c, F (mOrbitMap ρ v c) = mOrbitMap σ w c := by
    intro c
    have : e.symm (mOrbitMap ρ v c) = Submodule.Quotient.mk c := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
  have hFint : ∀ g x, F (ρ g x) = σ g (F x) := by
    intro g x
    obtain ⟨c, rfl⟩ := hsurj x
    rw [← mOrbitMap_mapDomain, hF, hF, mOrbitMap_mapDomain]
  let Fi : Representation.IntertwiningMap ρ σ := ⟨F, fun g => LinearMap.ext fun x => hFint g x⟩
  have hFi0 : Fi ≠ 0 := by
    intro h0
    have h1 : F v = w := by
      have := hF (Finsupp.single 1 1)
      rwa [mOrbitMap_single, mOrbitMap_single, one_smul, one_smul, map_one,
        Module.End.one_apply, map_one, Module.End.one_apply] at this
    have h2 : F v = 0 := by
      have : Fi v = 0 := by rw [h0]; rfl
      exact this
    apply hg₀
    rw [h, ← h1, h2, map_zero, map_zero]
  rcases Representation.IsIrreducible.bijective_or_eq_zero Fi with hb | h0
  · exact ⟨Representation.Equiv.mk (LinearEquiv.ofBijective F hb)
      fun g => LinearMap.ext fun x => hFint g x⟩
  · exact absurd h0 hFi0
end GroundTheory.Automorphic.RestrictedTensor
