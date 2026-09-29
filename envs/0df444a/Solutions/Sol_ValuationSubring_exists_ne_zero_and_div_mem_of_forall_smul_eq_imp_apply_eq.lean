-- Prove2me | solution 1 for ValuationSubring.exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7ae2647e-d0d4-502c-9f4d-6863f18e8823

import Mathlib
import Theorems.Thm_Ideal_ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
import Theorems.Thm_ValuationSubring_integralClosure_le_and_exists_ideal_mem_iff_mem_nonunits_and_mem_iff_exists_of_isDiscreteValuationRing
import Theorems.Thm_IsDedekindDomain_exists_zpow_mul_div_of_ramificationIdx_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq

set_option autoImplicit false

universe u

open scoped Pointwise

namespace VALFINAux

theorem isTorsionFree_of_injective {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] [IsDomain S] [Algebra R S]
    (h : Function.Injective (algebraMap R S)) : Module.IsTorsionFree R S :=
  Module.IsTorsionFree.of_smul_eq_zero (fun r m hm => by
    rw [Algebra.smul_def, mul_eq_zero] at hm
    rcases hm with h1 | h1
    · left; exact h (by rw [h1, map_zero])
    · right; exact h1)

theorem inv_mem_of_not_mem_nonunits {M : Type*} [Field M] (V : ValuationSubring M) {x : M}
    (hx : x ∉ V.nonunits) : x⁻¹ ∈ V := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hx
  exact hx.2

theorem ne_zero_of_not_mem_nonunits {M : Type*} [Field M] (V : ValuationSubring M) {x : M}
    (hx : x ∉ V.nonunits) : x ≠ 0 := by
  rintro rfl; exact hx V.nonunits.zero_mem

end VALFINAux

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    {C : Type u} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type u) [Field K] [Algebra C K] [IsFractionRing C K]
    {M : Type u} [Field M] [Algebra K M] [Algebra C M] [IsScalarTower C K M]
    [FiniteDimensional K M] [IsGalois K M]
    (V : ValuationSubring M) (hCV : ∀ c : C, algebraMap C M c ∈ V)
    (hCVmax : ∀ c : C, algebraMap C M c ∈ V.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C)
    (z : M) (hz : z ≠ 0)
    (hfix : ∀ σ : M ≃ₐ[K] M, σ • V = V → σ z = z) :
    ∃ c : K, c ≠ 0 ∧ z * (algebraMap K M c)⁻¹ ∈ V ∧ algebraMap K M c * z⁻¹ ∈ V := by
  classical
  haveI : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.of_finite K M

  have hinjCK : Function.Injective (algebraMap C K) := IsFractionRing.injective C K
  have hinjCM : Function.Injective (algebraMap C M) := by
    rw [IsScalarTower.algebraMap_eq C K M]; exact (algebraMap K M).injective.comp hinjCK

  haveI : IsIntegralClosure ↥(integralClosure C M) C M := inferInstance
  haveI hBfin : Module.Finite C ↥(integralClosure C M) := IsIntegralClosure.finite C K M ↥(integralClosure C M)
  haveI hBded : IsDedekindDomain ↥(integralClosure C M) := IsIntegralClosure.isDedekindDomain C K M ↥(integralClosure C M)
  haveI : IsFractionRing ↥(integralClosure C M) M :=
    IsIntegralClosure.isFractionRing_of_finite_extension C K M ↥(integralClosure C M)
  have hinjCB : Function.Injective (algebraMap C ↥(integralClosure C M)) := by
    intro a b h; apply hinjCM
    rw [IsScalarTower.algebraMap_apply C ↥(integralClosure C M) M, IsScalarTower.algebraMap_apply C ↥(integralClosure C M) M, h]
  haveI : Module.IsTorsionFree C ↥(integralClosure C M) := VALFINAux.isTorsionFree_of_injective hinjCB
  letI instG : MulSemiringAction (M ≃ₐ[K] M) ↥(integralClosure C M) :=
    IsIntegralClosure.MulSemiringAction C K M ↥(integralClosure C M)
  haveI : IsGaloisGroup (M ≃ₐ[K] M) C ↥(integralClosure C M) :=
    IsGaloisGroup.of_isFractionRing (M ≃ₐ[K] M) C ↥(integralClosure C M) K M
  have hsmulB : ∀ (σ : M ≃ₐ[K] M) (b : ↥(integralClosure C M)),
      ((σ • b : ↥(integralClosure C M)) : M) = σ (b : M) := fun σ b => algebraMap_galRestrict_apply C σ b

  obtain ⟨hBV, P, hPmax, hPover, hPmem, hVloc⟩ :=
    ValuationSubring.integralClosure_le_and_exists_ideal_mem_iff_mem_nonunits_and_mem_iff_exists_of_isDiscreteValuationRing
      K V hCV hCVmax
  haveI := hPmax
  haveI := hPover

  have hHV : ∀ σ : M ≃ₐ[K] M, σ ∈ MulAction.stabilizer (M ≃ₐ[K] M) P → σ • V = V := by
    intro σ hσ
    have hσP : σ • P = P := hσ

    have hfwd : ∀ (τ : M ≃ₐ[K] M), τ • P = P → ∀ y : M, y ∈ V → τ y ∈ V := by
      intro τ hτ y hy
      obtain ⟨b, s, hs, hys⟩ := (hVloc y).mp hy
      refine (hVloc (τ y)).mpr ⟨τ • b, τ • s, ?_, ?_⟩
      · intro h
        apply hs
        have : τ • s ∈ τ • P := by rw [hτ]; exact h
        exact Ideal.smul_mem_pointwise_smul_iff.mp this
      · rw [hsmulB, hsmulB, ← map_mul, hys]
    ext y
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hfwd σ hσP v hv
    · intro hy
      refine ⟨σ⁻¹ • y, ?_, by simp⟩
      have hσP' : σ⁻¹ • P = P := by
        rw [inv_smul_eq_iff, hσP]
      exact hfwd σ⁻¹ hσP' y hy

  set H : Subgroup (M ≃ₐ[K] M) := MulAction.stabilizer (M ≃ₐ[K] M) P with hH
  let Z : IntermediateField K M := FixedPoints.intermediateField ↥H
  have hzZ : z ∈ Z := fun h => hfix h (hHV h h.2)
  haveI : IsGaloisGroup ↥H ↥Z M := IsGaloisGroup.subgroup (M ≃ₐ[K] M) K M H

  haveI : IsScalarTower C ↥Z M := IsScalarTower.of_algebraMap_eq (fun c => rfl)
  haveI : IsScalarTower C K ↥Z := IsScalarTower.of_algebraMap_eq (fun c => Subtype.ext (by
    show algebraMap C M c = algebraMap K M (algebraMap C K c)
    exact IsScalarTower.algebraMap_apply C K M c))
  have hinjCZ : Function.Injective (algebraMap C ↥Z) := by
    intro a b h; apply hinjCM
    rw [IsScalarTower.algebraMap_apply C ↥Z M, IsScalarTower.algebraMap_apply C ↥Z M, h]

  haveI : IsIntegralClosure ↥(integralClosure C ↥Z) C ↥Z := inferInstance
  haveI : Module.Finite C ↥(integralClosure C ↥Z) := IsIntegralClosure.finite C K ↥Z ↥(integralClosure C ↥Z)
  haveI : IsDedekindDomain ↥(integralClosure C ↥Z) := IsIntegralClosure.isDedekindDomain C K ↥Z ↥(integralClosure C ↥Z)
  haveI : IsFractionRing ↥(integralClosure C ↥Z) ↥Z :=
    IsIntegralClosure.isFractionRing_of_finite_extension C K ↥Z ↥(integralClosure C ↥Z)
  have hinjCZ' : Function.Injective (algebraMap C ↥(integralClosure C ↥Z)) := by
    intro a b h; apply hinjCZ
    rw [IsScalarTower.algebraMap_apply C ↥(integralClosure C ↥Z) ↥Z,
      IsScalarTower.algebraMap_apply C ↥(integralClosure C ↥Z) ↥Z, h]

  let f : ↥(integralClosure C ↥Z) →+* ↥(integralClosure C M) :=
    { toFun := fun b => ⟨algebraMap ↥Z M (b : ↥Z),
        (mem_integralClosure_iff C M).mpr ((mem_integralClosure_iff C ↥Z).mp b.2).algebraMap⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hf : ∀ b : ↥(integralClosure C ↥Z), ((f b : ↥(integralClosure C M)) : M) = algebraMap ↥Z M (b : ↥Z) :=
    fun _ => rfl
  have hfinj : Function.Injective f := by
    intro a b hab
    have := congrArg (fun x : ↥(integralClosure C M) => (x : M)) hab
    simp only [hf] at this
    exact Subtype.ext ((algebraMap ↥Z M).injective this)
  letI : Algebra ↥(integralClosure C ↥Z) ↥(integralClosure C M) := f.toAlgebra
  haveI : IsScalarTower C ↥(integralClosure C ↥Z) ↥(integralClosure C M) :=
    IsScalarTower.of_algebraMap_eq (fun c => Subtype.ext (by
      show algebraMap C M c = algebraMap ↥Z M (algebraMap C ↥Z c : ↥Z)
      rw [IsScalarTower.algebraMap_apply C ↥Z M]))
  haveI : IsScalarTower ↥(integralClosure C ↥Z) ↥Z M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥(integralClosure C ↥Z) ↥(integralClosure C M) M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite ↥(integralClosure C ↥Z) ↥(integralClosure C M) :=
    Module.Finite.of_restrictScalars_finite C ↥(integralClosure C ↥Z) ↥(integralClosure C M)
  haveI : Module.IsTorsionFree ↥(integralClosure C ↥Z) ↥(integralClosure C M) :=
    VALFINAux.isTorsionFree_of_injective hfinj
  haveI : Algebra.IsIntegral ↥(integralClosure C ↥Z) ↥(integralClosure C M) :=
    Algebra.IsIntegral.tower_top (R := C)
  haveI : SMulDistribClass ↥H ↥(integralClosure C M) M := ⟨fun h b m => by
    show ((h : M ≃ₐ[K] M) • ((b : M) * m)) = ((((h : M ≃ₐ[K] M) • b : ↥(integralClosure C M)) : M) * ((h : M ≃ₐ[K] M) • m))
    rw [smul_mul', hsmulB]; rfl⟩
  haveI : IsGaloisGroup ↥H ↥(integralClosure C ↥Z) ↥(integralClosure C M) :=
    IsGaloisGroup.of_isFractionRing ↥H ↥(integralClosure C ↥Z) ↥(integralClosure C M) ↥Z M

  have hm0 : IsLocalRing.maximalIdeal C ≠ ⊥ := IsDiscreteValuationRing.not_a_field C
  have hef := Ideal.ramificationIdx_under_eq_one_and_inertiaDeg_under_eq_one_of_isGaloisGroup_stabilizer
    (A := C) (B := ↥(integralClosure C ↥Z)) (C := ↥(integralClosure C M)) (M ≃ₐ[K] M)
    (IsLocalRing.maximalIdeal C) hm0 P

  set VZ : ValuationSubring ↥Z := V.comap (algebraMap ↥Z M) with hVZ
  have hnuZ : ∀ x : ↥Z, x ∈ VZ.nonunits ↔ algebraMap ↥Z M x ∈ V.nonunits := by
    intro x
    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, hVZ, ValuationSubring.mem_comap,
      map_inv₀, map_eq_zero_iff _ (algebraMap ↥Z M).injective]
  have hCVZ : ∀ c : C, algebraMap C ↥Z c ∈ VZ := by
    intro c; rw [hVZ, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply C ↥Z M]; exact hCV c
  have hCVmaxZ : ∀ c : C, algebraMap C ↥Z c ∈ VZ.nonunits ↔ c ∈ IsLocalRing.maximalIdeal C := by
    intro c; rw [hnuZ, ← IsScalarTower.algebraMap_apply C ↥Z M]; exact hCVmax c
  haveI : Algebra.IsSeparable K ↥Z := Algebra.isSeparable_tower_bot_of_isSeparable K ↥Z M
  obtain ⟨hBZV, PZ, hPZmax, hPZover, hPZmem, hVZloc⟩ :=
    ValuationSubring.integralClosure_le_and_exists_ideal_mem_iff_mem_nonunits_and_mem_iff_exists_of_isDiscreteValuationRing
      K VZ hCVZ hCVmaxZ
  haveI := hPZmax
  haveI := hPZover

  have hPZeq : P.under ↥(integralClosure C ↥Z) = PZ := by
    ext b
    rw [Ideal.under_def, Ideal.mem_comap, hPZmem, hnuZ, hPmem]
    rfl
  have he1 : Ideal.ramificationIdx' (IsLocalRing.maximalIdeal C) PZ = 1 := by rw [← hPZeq]; exact hef.1

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible C
  have hp : IsLocalRing.maximalIdeal C = Ideal.span {π} := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hPZ0 : PZ ≠ ⊥ := by
    intro h0
    apply hm0
    rw [hPZover.over, h0]
    exact Ideal.comap_bot_of_injective _ hinjCZ'
  have hpq : Ideal.map (algebraMap C ↥(integralClosure C ↥Z)) (IsLocalRing.maximalIdeal C) ≤ PZ :=
    Ideal.map_le_iff_le_comap.mpr (le_of_eq hPZover.over)
  have hz' : (⟨z, hzZ⟩ : ↥Z) ≠ 0 := fun h => hz (congrArg Subtype.val h)
  obtain ⟨n, b, s, hb, hs, heq⟩ := IsDedekindDomain.exists_zpow_mul_div_of_ramificationIdx_eq_one
    π (IsLocalRing.maximalIdeal C) hp PZ hPZ0 hpq he1 ↥Z ⟨z, hzZ⟩ hz'

  set S : M := algebraMap ↥Z M (algebraMap ↥(integralClosure C ↥Z) ↥Z s) with hS
  set Bb : M := algebraMap ↥Z M (algebraMap ↥(integralClosure C ↥Z) ↥Z b) with hBb
  set ϖ : M := algebraMap C M π with hϖ
  have heqM : z * S = ϖ ^ n * Bb := by
    have := congrArg (algebraMap ↥Z M) heq
    rw [map_mul, map_mul, map_zpow₀, ← IsScalarTower.algebraMap_apply C ↥Z M] at this
    exact this
  have hSV : S ∈ V := hBZV s
  have hBbV : Bb ∈ V := hBZV b
  have hSnu : S ∉ V.nonunits := fun h => hs ((hPZmem s).mpr ((hnuZ _).mpr h))
  have hBbnu : Bb ∉ V.nonunits := fun h => hb ((hPZmem b).mpr ((hnuZ _).mpr h))
  have hS0 : S ≠ 0 := VALFINAux.ne_zero_of_not_mem_nonunits V hSnu
  have hBb0 : Bb ≠ 0 := VALFINAux.ne_zero_of_not_mem_nonunits V hBbnu
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hϖ0 : ϖ ≠ 0 := fun h => hπ0 (hinjCM (by rw [← hϖ, h, map_zero]))
  have hϖn : ϖ ^ n ≠ 0 := zpow_ne_zero n hϖ0
  refine ⟨algebraMap C K π ^ n, zpow_ne_zero n (fun h => hπ0 (hinjCK (by rw [h, map_zero]))), ?_, ?_⟩
  · have hc : algebraMap K M (algebraMap C K π ^ n) = ϖ ^ n := by
      rw [map_zpow₀, ← IsScalarTower.algebraMap_apply C K M]
    rw [hc]
    have hz1 : z = ϖ ^ n * Bb * S⁻¹ := by rw [eq_mul_inv_iff_mul_eq₀ hS0]; exact heqM
    have e1 : z * (ϖ ^ n)⁻¹ = Bb * S⁻¹ := by
      rw [hz1]
      calc ϖ ^ n * Bb * S⁻¹ * (ϖ ^ n)⁻¹ = (ϖ ^ n * (ϖ ^ n)⁻¹) * (Bb * S⁻¹) := by ring
        _ = Bb * S⁻¹ := by rw [mul_inv_cancel₀ hϖn, one_mul]
    rw [e1]
    exact mul_mem hBbV (VALFINAux.inv_mem_of_not_mem_nonunits V hSnu)
  · have hc : algebraMap K M (algebraMap C K π ^ n) = ϖ ^ n := by
      rw [map_zpow₀, ← IsScalarTower.algebraMap_apply C K M]
    rw [hc]
    have hz1 : z = ϖ ^ n * Bb * S⁻¹ := by rw [eq_mul_inv_iff_mul_eq₀ hS0]; exact heqM
    have e2 : ϖ ^ n * z⁻¹ = S * Bb⁻¹ := by
      rw [hz1, mul_inv, mul_inv, inv_inv]
      calc ϖ ^ n * ((ϖ ^ n)⁻¹ * Bb⁻¹ * S) = (ϖ ^ n * (ϖ ^ n)⁻¹) * (S * Bb⁻¹) := by ring
        _ = S * Bb⁻¹ := by rw [mul_inv_cancel₀ hϖn, one_mul]
    rw [e2]
    exact mul_mem hSV (VALFINAux.inv_mem_of_not_mem_nonunits V hBbnu)

end S_ValuationSubring_exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq
end P2MW
export P2MW.S_ValuationSubring_exists_ne_zero_and_div_mem_of_forall_smul_eq_imp_apply_eq (solution)
