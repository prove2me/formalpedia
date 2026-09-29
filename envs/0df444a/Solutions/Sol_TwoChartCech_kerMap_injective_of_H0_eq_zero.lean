-- Prove2me | solution 1 for TwoChartCech.kerMap_injective_of_H0_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d2f89097-fa39-5ec2-833a-04389788a166

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_kerMap_injective_of_H0_eq_zero

set_option autoImplicit false

universe u

namespace TwoChartCech
namespace Snake
p2m_open "TwoChartCech"

variable {R : Type u} [CommRing R]
    {K0 K1 E0 E1 S0 S1 : Type u}
    [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
    [AddCommGroup E0] [Module R E0] [AddCommGroup E1] [Module R E1]
    [AddCommGroup S0] [Module R S0] [AddCommGroup S1] [Module R S1]
    (dK : K0 →ₗ[R] K1) (dE : E0 →ₗ[R] E1) (dS : S0 →ₗ[R] S1)
    (i0 : K0 →ₗ[R] E0) (i1 : K1 →ₗ[R] E1) (p0 : E0 →ₗ[R] S0) (p1 : E1 →ₗ[R] S1)
    (hi : dE ∘ₗ i0 = i1 ∘ₗ dK) (hp : dS ∘ₗ p0 = p1 ∘ₗ dE)
    (hi1 : Function.Injective i1) (hp0 : Function.Surjective p0)
    (hex0 : LinearMap.range i0 = LinearMap.ker p0) (hex1 : LinearMap.range i1 = LinearMap.ker p1)
    (hE : LinearMap.ker dE = ⊥)

include hi hp hi1 hp0 hex0 hex1 hE in

theorem exists_injective_linearMap :
    ∃ δ : LinearMap.ker dS →ₗ[R] (K1 ⧸ LinearMap.range dK), Function.Injective δ := by
  classical

  have step : ∀ s : LinearMap.ker dS, ∃ k : K1, ∃ e : E0, p0 e = s ∧ dE e = i1 k := by
    intro s
    obtain ⟨e, he⟩ := hp0 s
    have : dE e ∈ LinearMap.ker p1 := by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← hp, LinearMap.comp_apply, he]
      exact s.2
    rw [← hex1] at this
    obtain ⟨k, hk⟩ := this
    exact ⟨k, e, he, hk.symm⟩
  choose kOf eOf hpe hde using step

  have well : ∀ (s : LinearMap.ker dS) (k : K1) (e : E0), p0 e = s → dE e = i1 k →
      (Submodule.Quotient.mk k : K1 ⧸ LinearMap.range dK) = Submodule.Quotient.mk (kOf s) := by
    intro s k e he hde'
    have hdiff : e - eOf s ∈ LinearMap.ker p0 := by
      rw [LinearMap.mem_ker, map_sub, he, hpe, sub_self]
    rw [← hex0] at hdiff
    obtain ⟨x, hx⟩ := hdiff
    rw [Submodule.Quotient.eq]
    refine ⟨x, hi1 ?_⟩
    have h1 : i1 (dK x) = dE (i0 x) := (LinearMap.congr_fun hi x).symm
    rw [h1, hx, map_sub, hde', hde, map_sub]
  refine ⟨{ toFun := fun s => Submodule.Quotient.mk (kOf s), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro s t
    show (Submodule.Quotient.mk (kOf (s + t)) : K1 ⧸ LinearMap.range dK)
      = Submodule.Quotient.mk (kOf s) + Submodule.Quotient.mk (kOf t)
    rw [← Submodule.Quotient.mk_add]
    exact (well (s + t) (kOf s + kOf t) (eOf s + eOf t)
      (by rw [map_add, hpe, hpe]; rfl) (by rw [map_add, hde, hde, map_add])).symm
  · intro r s
    show (Submodule.Quotient.mk (kOf (r • s)) : K1 ⧸ LinearMap.range dK) = r • Submodule.Quotient.mk (kOf s)
    rw [← Submodule.Quotient.mk_smul]
    exact (well (r • s) (r • kOf s) (r • eOf s)
      (by rw [map_smul, hpe]; rfl) (by rw [map_smul, hde, map_smul])).symm
  ·
    intro s t hst

    have key : ∀ s : LinearMap.ker dS, (Submodule.Quotient.mk (kOf s) : K1 ⧸ LinearMap.range dK) = 0 → s = 0 := by
      intro s hs
      rw [Submodule.Quotient.mk_eq_zero] at hs
      obtain ⟨x, hx⟩ := hs
      have : eOf s - i0 x ∈ LinearMap.ker dE := by
        have h2 : dE (i0 x) = i1 (dK x) := LinearMap.congr_fun hi x
        rw [LinearMap.mem_ker, map_sub, hde, ← hx, h2, sub_self]
      rw [hE, Submodule.mem_bot, sub_eq_zero] at this
      apply Subtype.ext
      rw [← hpe s, this]
      have : p0 (i0 x) = 0 := by
        have hmem : i0 x ∈ LinearMap.ker p0 := by rw [← hex0]; exact LinearMap.mem_range_self _ _
        exact hmem
      rw [this]; rfl

    have hsub : (Submodule.Quotient.mk (kOf (s - t)) : K1 ⧸ LinearMap.range dK)
        = Submodule.Quotient.mk (kOf s) - Submodule.Quotient.mk (kOf t) := by
      rw [← Submodule.Quotient.mk_sub]
      exact (well (s - t) (kOf s - kOf t) (eOf s - eOf t)
        (by rw [map_sub, hpe, hpe]; rfl) (by rw [map_sub, hde, hde, map_sub])).symm
    have h0 : (Submodule.Quotient.mk (kOf (s - t)) : K1 ⧸ LinearMap.range dK) = 0 := by
      rw [hsub]; exact sub_eq_zero.mpr hst
    exact sub_eq_zero.mp (key (s - t) h0)

end TwoChartCech.Snake

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {K0 K1 E0 E1 S0 S1 : Type u}
    [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1]
    [AddCommGroup E0] [Module R E0] [AddCommGroup E1] [Module R E1]
    [AddCommGroup S0] [Module R S0] [AddCommGroup S1] [Module R S1]
    (dK : K0 →ₗ[R] K1) (dE : E0 →ₗ[R] E1) (dS : S0 →ₗ[R] S1)
    (i0 : K0 →ₗ[R] E0) (i1 : K1 →ₗ[R] E1) (p0 : E0 →ₗ[R] S0) (p1 : E1 →ₗ[R] S1)
    (hi : dE ∘ₗ i0 = i1 ∘ₗ dK) (hp : dS ∘ₗ p0 = p1 ∘ₗ dE)
    (hi0 : Function.Injective i0) (hi1 : Function.Injective i1)
    (hp0 : Function.Surjective p0) (hp1 : Function.Surjective p1)
    (hex0 : LinearMap.range i0 = LinearMap.ker p0) (hex1 : LinearMap.range i1 = LinearMap.ker p1)
    (hE : LinearMap.ker dE = ⊥) [Module.Finite R (K1 ⧸ LinearMap.range dK)] :
    Module.Finite R (LinearMap.ker dS) := by
  obtain ⟨δ, hδ⟩ := TwoChartCech.Snake.exists_injective_linearMap dK dE dS i0 i1 p0 p1 hi hp hi1 hp0 hex0 hex1 hE
  exact Module.Finite.of_injective δ hδ

end S_TwoChartCech_kerMap_injective_of_H0_eq_zero
end P2MW
export P2MW.S_TwoChartCech_kerMap_injective_of_H0_eq_zero (solution)
