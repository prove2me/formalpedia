-- Prove2me | solution 1 for WeierstrassCurve.IsTwoKernel.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/0588c805-5919-5664-8fbc-9885a3f2f261

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Theorems.Thm_Polynomial_existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_IsTwoKernel_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot

set_option autoImplicit false

universe u

open Polynomial

namespace TwoKerLiftAux

variable {R : Type u} [CommRing R]

theorem resultant_certificate (W : WeierstrassCurve R) (x : R) :
    ((-2*W.a₁^6 - 24*W.a₁^4*W.a₂ + 60*W.a₁^3*W.a₃ - 96*W.a₁^2*W.a₂^2 + 120*W.a₁^2*W.a₄ + 240*W.a₁*W.a₂*W.a₃ - 128*W.a₂^3
        + 480*W.a₂*W.a₄ - 216*W.a₃^2 - 864*W.a₆)
      + (-12*W.a₁^4 - 96*W.a₁^2*W.a₂ + 288*W.a₁*W.a₃ - 192*W.a₂^2 + 576*W.a₄) * x)
      * (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆)
    + ((W.a₁^5*W.a₃ + 2*W.a₁^4*W.a₄ + 8*W.a₁^3*W.a₂*W.a₃ + 16*W.a₁^2*W.a₂*W.a₄ - 26*W.a₁^2*W.a₃^2 + 24*W.a₁^2*W.a₆
        + 16*W.a₁*W.a₂^2*W.a₃ - 128*W.a₁*W.a₃*W.a₄ + 32*W.a₂^2*W.a₄ + 24*W.a₂*W.a₃^2 + 96*W.a₂*W.a₆ - 128*W.a₄^2)
      + (W.a₁^6 + 12*W.a₁^4*W.a₂ - 28*W.a₁^3*W.a₃ + 48*W.a₁^2*W.a₂^2 - 56*W.a₁^2*W.a₄ - 112*W.a₁*W.a₂*W.a₃ + 64*W.a₂^3
        - 224*W.a₂*W.a₄ + 72*W.a₃^2 + 288*W.a₆) * x
      + (4*W.a₁^4 + 32*W.a₁^2*W.a₂ - 96*W.a₁*W.a₃ + 64*W.a₂^2 - 192*W.a₄) * x ^ 2)
      * (12 * x ^ 2 + 2 * W.b₂ * x + 2 * W.b₄)
    = 8 * W.Δ := by
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.Δ]
  ring

theorem eval_Ψ₂Sq (W : WeierstrassCurve R) (x : R) :
    W.Ψ₂Sq.eval x = 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
  simp [WeierstrassCurve.Ψ₂Sq]

theorem eval_derivative_Ψ₂Sq (W : WeierstrassCurve R) (x : R) :
    W.Ψ₂Sq.derivative.eval x = 12 * x ^ 2 + 2 * W.b₂ * x + 2 * W.b₄ := by
  simp [WeierstrassCurve.Ψ₂Sq]
  ring

theorem isUnit_eval_derivative_Ψ₂Sq (W : WeierstrassCurve R) (h2 : IsUnit (2 : R)) (hΔ : IsUnit W.Δ) (c : R)
    (hc : W.Ψ₂Sq.eval c = 0) : IsUnit (W.Ψ₂Sq.derivative.eval c) := by
  have key := resultant_certificate W c
  rw [← eval_Ψ₂Sq, ← eval_derivative_Ψ₂Sq, hc, mul_zero, zero_add] at key
  have h8 : IsUnit (8 * W.Δ) := by
    refine IsUnit.mul ?_ hΔ
    have : (8 : R) = 2 ^ 3 := by norm_num
    rw [this]; exact h2.pow 3
  rw [← key] at h8
  exact isUnit_of_mul_isUnit_right h8

theorem isCoprime_X_sub_C_of_isUnit_eval {g : R[X]} {c : R} (h : IsUnit (g.eval c)) : IsCoprime (X - C c) g := by
  obtain ⟨u, hu⟩ := h
  have hdecomp : g %ₘ (X - C c) + (X - C c) * (g /ₘ (X - C c)) = g := modByMonic_add_div g (X - C c)
  rw [modByMonic_X_sub_C_eq_C_eval] at hdecomp
  have e : C (g.eval c) = g - (X - C c) * (g /ₘ (X - C c)) := eq_sub_of_add_eq hdecomp
  refine ⟨-(C (↑u⁻¹ : R) * (g /ₘ (X - C c))), C (↑u⁻¹ : R), ?_⟩
  calc -(C (↑u⁻¹ : R) * (g /ₘ (X - C c))) * (X - C c) + C (↑u⁻¹ : R) * g
      = C (↑u⁻¹ : R) * (g - (X - C c) * (g /ₘ (X - C c))) := by ring
    _ = C (↑u⁻¹ : R) * C (g.eval c) := by rw [e]
    _ = 1 := by rw [← C_mul, ← hu, Units.inv_mul, C_1]

theorem nontrivial_of_surjective_of_ker_pow_eq_bot {T T' : Type u} [CommRing T] [CommRing T'] [Nontrivial T]
    (π : T →+* T') (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥) : Nontrivial T' := by
  by_contra htriv
  rw [not_nontrivial_iff_subsingleton] at htriv
  obtain ⟨n, hn⟩ := hnil
  have h1 : (1 : T) ^ n ∈ RingHom.ker π ^ n :=
    Ideal.pow_mem_pow (by rw [RingHom.mem_ker]; exact Subsingleton.elim _ _) n
  rw [hn, one_pow, Ideal.mem_bot] at h1
  exact one_ne_zero h1

end TwoKerLiftAux

open TwoKerLiftAux in

theorem solution
    {T T' : Type u} [CommRing T] [CommRing T'] (π : T →+* T') (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (W : WeierstrassCurve T) (hΔ : IsUnit W.Δ) (h2 : IsUnit (2 : T))
    (h' : Polynomial T') (hh' : (W.map π).IsTwoKernel h') :
    ∃! h : Polynomial T, h.map π = h' ∧ W.IsTwoKernel h := by

  rcases subsingleton_or_nontrivial T with hT | hT
  · haveI := hT
    haveI : Subsingleton T[X] := inferInstance
    have hT' : Subsingleton T' := hπ.subsingleton
    haveI : Subsingleton T'[X] := inferInstance
    refine ⟨0, ⟨Subsingleton.elim _ _, ⟨by simp, Subsingleton.elim _ _, ⟨0, Subsingleton.elim _ _⟩⟩⟩,
      fun _ _ => Subsingleton.elim _ _⟩
  haveI : Nontrivial T' := nontrivial_of_surjective_of_ker_pow_eq_bot π hnil

  set c : T' := -h'.coeff 0 with hc
  have hh'eq : h' = X - C c := by
    have e := eq_X_add_C_of_natDegree_le_one hh'.natDegree_le
    rw [hh'.coeff_eq_one, C_1, one_mul] at e
    rw [e, hc, C_neg, sub_neg_eq_add]

  obtain ⟨g', hg'⟩ := hh'.dvd_Ψ₂Sq
  have hfmap : W.Ψ₂Sq.map π = h' * g' := by rw [← WeierstrassCurve.map_Ψ₂Sq, hg']
  have h2' : IsUnit (2 : T') := by have e := h2.map π; rwa [map_ofNat] at e
  have hΔ' : IsUnit (W.map π).Δ := by rw [WeierstrassCurve.map_Δ]; exact hΔ.map π
  have hroot : (W.map π).Ψ₂Sq.eval c = 0 := by
    rw [hg', hh'eq, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
  have hder : (W.map π).Ψ₂Sq.derivative.eval c = g'.eval c := by
    rw [hg', hh'eq, derivative_mul, derivative_X_sub_C, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self,
      zero_mul, add_zero]
  have hunit : IsUnit (g'.eval c) := by
    rw [← hder]; exact isUnit_eval_derivative_Ψ₂Sq _ h2' hΔ' c hroot
  have hcop : IsCoprime h' g' := by rw [hh'eq]; exact isCoprime_X_sub_C_of_isUnit_eval hunit

  obtain ⟨h, ⟨hmonic, hmap, hdvd⟩, huniq⟩ :=
    Polynomial.existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot π hπ hnil W.Ψ₂Sq h' g'
      (WeierstrassCurve.IsTwoKernel.monic _ hh') hcop hfmap
  have hnat' : h'.natDegree = 1 :=
    le_antisymm hh'.natDegree_le (le_natDegree_of_ne_zero (by rw [hh'.coeff_eq_one]; exact one_ne_zero))
  have hnat : h.natDegree = 1 := by rw [← hmonic.natDegree_map π, hmap, hnat']
  refine ⟨h, ⟨hmap, ⟨hnat.le, ?_, hdvd⟩⟩, ?_⟩
  · have e := hmonic.coeff_natDegree
    rwa [hnat] at e
  · rintro h₂ ⟨hmap₂, hh₂⟩
    exact huniq h₂ ⟨WeierstrassCurve.IsTwoKernel.monic _ hh₂, hmap₂, hh₂.dvd_Ψ₂Sq⟩

end S_WeierstrassCurve_IsTwoKernel_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
end P2MW
export P2MW.S_WeierstrassCurve_IsTwoKernel_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot (solution)
