-- Prove2me | solution 1 for UnphysicalHilbert.prop21_unitary_leaves_domain
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:47:00.738212+00:00
-- url     : https://prove2.me/submissions/b026d445-7a2c-42de-adf7-a06da8549d3e

import Mathlib

namespace UHAux

lemma bounded_of_complete
    {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (X : H →ₗ.[ℂ] Y) (hX : X.IsClosed) (hc : CompleteSpace X.domain) :
    ∃ C : ℝ, ∀ x : X.domain, ‖X x‖ ≤ C * ‖(x : H)‖ := by
  set f : X.domain →ₗ[ℂ] Y := X.toFun
  have hg : (f.graph : Set (X.domain × Y)) =
      (fun p : X.domain × Y => ((p.1 : H), p.2)) ⁻¹' (X.graph : Set (H × Y)) := by
    ext p
    simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_preimage]
    rw [LinearPMap.mem_graph_iff]
    constructor
    · intro h; exact ⟨p.1, rfl, h.symm⟩
    · rintro ⟨y, hy, h⟩
      have : y = p.1 := Subtype.ext hy
      subst this; exact h.symm
  have hcl : IsClosed (f.graph : Set (X.domain × Y)) := by
    rw [hg]
    exact hX.preimage (by fun_prop)
  have hcont := f.continuous_of_isClosed_graph hcl
  set F : X.domain →L[ℂ] Y := ⟨f, hcont⟩
  refine ⟨‖F‖, fun x => ?_⟩
  have := F.le_opNorm x
  exact this

end UHAux

open UHAux in
theorem solution
    {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]
    (X : H →ₗ.[ℂ] Y) (hX : X.IsClosed)
    (hunb : ¬ ∃ C : ℝ, ∀ x : X.domain, ‖X x‖ ≤ C * ‖(x : H)‖) :
    ∃ U : H ≃ₗᵢ[ℂ] H, ∃ x ∈ X.domain, U x ∉ X.domain := by
  -- the domain is a proper subspace
  have hne : X.domain ≠ ⊤ := by
    intro htop
    apply hunb
    apply bounded_of_complete X hX
    have : IsClosed (X.domain : Set H) := by rw [htop]; exact isClosed_univ
    exact this.completeSpace_coe
  obtain ⟨z, hz⟩ : ∃ z, z ∉ X.domain := by
    by_contra h; push Not at h
    exact hne (eq_top_iff.mpr fun x _ => h x)
  -- the domain contains a nonzero vector
  obtain ⟨x0, hx0, hx0ne⟩ : ∃ x0 ∈ X.domain, x0 ≠ 0 := by
    by_contra h; push Not at h
    apply hunb
    refine ⟨0, fun x => ?_⟩
    have : x = 0 := Subtype.ext (h x x.2)
    subst this; simp
  -- a vector outside the domain, not orthogonal to x0
  obtain ⟨v, hv, hvx⟩ : ∃ v, v ∉ X.domain ∧ inner ℂ v x0 ≠ 0 := by
    by_cases h : inner ℂ z x0 = 0
    · refine ⟨z + x0, fun hm => hz ?_, ?_⟩
      · have := X.domain.sub_mem hm hx0; simpa using this
      · rw [inner_add_left, h, zero_add, inner_self_ne_zero]; exact hx0ne
    · exact ⟨z, hz, h⟩
  have hv0 : v ≠ 0 := by rintro rfl; exact hv X.domain.zero_mem
  refine ⟨(ℂ ∙ v).reflection, x0, hx0, fun hm => hv ?_⟩
  rw [Submodule.reflection_apply, Submodule.starProjection_singleton] at hm
  have h1 : (2 : ℕ) • ((inner ℂ v x0 / ((‖v‖ ^ 2 : ℝ) : ℂ)) • v) ∈ X.domain := by
    have := X.domain.add_mem hm hx0; simpa using this
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_ofNat] at h1
  have hc : (2 : ℂ) * (inner ℂ v x0 / ((‖v‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    apply mul_ne_zero two_ne_zero (div_ne_zero hvx _)
    exact_mod_cast (pow_pos (norm_pos_iff.mpr hv0) 2).ne'
  have := X.domain.smul_mem ((2 : ℂ) * (inner ℂ v x0 / ((‖v‖ ^ 2 : ℝ) : ℂ)))⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hc), one_smul] at this
