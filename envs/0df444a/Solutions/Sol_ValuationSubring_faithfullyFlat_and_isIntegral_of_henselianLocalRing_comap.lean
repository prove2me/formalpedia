-- Prove2me | solution 1 for ValuationSubring.faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/f6d5e1f6-ff8a-506d-b2d7-a44e383c1bfc

import Mathlib
import Theorems.Thm_HenselianLocalRing_isLocalRing_of_isDomain_of_moduleFinite
import Theorems.Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap

set_option autoImplicit false

universe u v

namespace ProlongIntAux

open IsLocalRing

theorem isIntegral_of_mem_valuationSubring
    {A₀ : Type*} [CommRing A₀] [IsDomain A₀] [IsNoetherianRing A₀] [Ring.KrullDimLE 1 A₀]
    [HenselianLocalRing A₀]
    {K₀ : Type*} [Field K₀] [Algebra A₀ K₀] [IsFractionRing A₀ K₀]
    {K₁ : Type*} [Field K₁] [Algebra A₀ K₁] [Algebra K₀ K₁] [IsScalarTower A₀ K₀ K₁] [FiniteDimensional K₀ K₁]
    (O : ValuationSubring K₁) (hA₀ : ∀ a : A₀, algebraMap A₀ K₁ a ∈ O) (hO : O ≠ ⊤)
    (x : K₁) (hx : x ∈ O) :
    IsIntegral A₀ x := by
  classical
  set B : Subalgebra A₀ K₁ := integralClosure A₀ K₁ with hB
  have hmemB : ∀ y : K₁, y ∈ B ↔ IsIntegral A₀ y := fun y => by rw [hB]; exact mem_integralClosure_iff A₀ K₁

  have hBO : ∀ y : K₁, y ∈ B → y ∈ O := by
    intro y hy
    letI : Algebra A₀ ↥O := ((algebraMap A₀ K₁).codRestrict O hA₀).toAlgebra
    haveI : IsScalarTower A₀ ↥O K₁ := IsScalarTower.of_algebraMap_eq (fun a => rfl)
    have hint : IsIntegral ↥O y := IsIntegral.tower_top ((hmemB y).mp hy)
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := ↥O) (K := K₁) hint
    rw [← hz]
    exact z.2

  obtain ⟨hBnoeth, hBdim, -⟩ :=
    Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite (A := A₀) (K := K₀) (L := K₁) B
  haveI : IsNoetherianRing ↥B := hBnoeth
  haveI : Ring.DimensionLEOne ↥B := hBdim
  haveI : Algebra.IsIntegral A₀ ↥B := by
    refine ⟨fun y => ?_⟩
    exact IsIntegral.tower_bot (A := ↥B) (B := K₁) Subtype.val_injective ((hmemB y).mp y.2)

  have hloc : IsLocalRing ↥B := by
    obtain ⟨𝔭, h𝔭⟩ := Ideal.exists_maximal ↥B
    refine IsLocalRing.of_unique_max_ideal ⟨𝔭, h𝔭, fun 𝔮 h𝔮 => ?_⟩
    by_contra hne
    have hnle : ¬ 𝔭 ≤ 𝔮 := fun hle => hne (h𝔭.eq_of_le h𝔮.ne_top hle).symm
    obtain ⟨b, hb𝔭, hb𝔮⟩ := Set.not_subset.mp (show ¬ ((𝔭 : Set ↥B) ⊆ 𝔮) from hnle)

    have hbint : IsIntegral A₀ (b : K₁) := (hmemB _).mp b.2
    haveI hSfin : Module.Finite A₀ ↥(Algebra.adjoin A₀ {(b : K₁)}) :=
      Algebra.finite_adjoin_simple_of_isIntegral hbint
    set S : Subalgebra A₀ K₁ := Algebra.adjoin A₀ {(b : K₁)} with hS
    have hSB : S ≤ B := by
      rw [hS, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      exact b.2
    haveI hSloc : IsLocalRing ↥S := HenselianLocalRing.isLocalRing_of_isDomain_of_moduleFinite (R := A₀)
    letI : Algebra ↥S ↥B := (Subalgebra.inclusion hSB).toRingHom.toAlgebra
    haveI : IsScalarTower A₀ ↥S ↥B := IsScalarTower.of_algebraMap_eq (fun a => rfl)
    haveI : Algebra.IsIntegral ↥S ↥B :=
      ⟨fun y => IsIntegral.tower_top (R := A₀) (A := ↥S) (Algebra.IsIntegral.isIntegral (R := A₀) y)⟩
    have h1 : (𝔭.comap (algebraMap ↥S ↥B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔭
    have h2 : (𝔮.comap (algebraMap ↥S ↥B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔮
    have hbS : (b : K₁) ∈ S := by rw [hS]; exact Algebra.subset_adjoin (Set.mem_singleton _)
    have hb1 : (⟨(b : K₁), hbS⟩ : ↥S) ∈ 𝔭.comap (algebraMap ↥S ↥B) := by
      rw [Ideal.mem_comap]
      convert hb𝔭
      rfl
    have heq : 𝔭.comap (algebraMap ↥S ↥B) = 𝔮.comap (algebraMap ↥S ↥B) := by
      rw [IsLocalRing.eq_maximalIdeal h1, IsLocalRing.eq_maximalIdeal h2]
    rw [heq, Ideal.mem_comap] at hb1
    apply hb𝔮
    first | exact hb1 | (convert hb1 using 1; rfl)
  haveI := hloc

  haveI : IsFractionRing ↥B K₁ :=
    IsIntegralClosure.isFractionRing_of_finite_extension A₀ K₀ K₁ ↥B
  haveI : IsIntegrallyClosed ↥B := by
    rw [hB]; exact integralClosure.isIntegrallyClosedOfFiniteExtension K₀

  have key : ∀ t : ↥B, t ≠ 0 → t ∈ maximalIdeal ↥B → ((t : K₁))⁻¹ ∈ O → False := by
    intro t ht0 htm hti
    apply hO
    ext y
    refine ⟨fun _ => ValuationSubring.mem_top y, fun _ => ?_⟩
    obtain ⟨b, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := ↥B) y
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs

    have htrad : t ∈ (Ideal.span {s}).radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      intro J hJ
      have hJne : J ≠ ⊥ := by
        intro hJ0
        apply hs0
        have : s ∈ J := hJ.1 (Ideal.subset_span (Set.mem_singleton s))
        rw [hJ0] at this
        exact (Submodule.mem_bot ↥B).mp this
      have hJmax : J.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hJne hJ.2
      rw [IsLocalRing.eq_maximalIdeal hJmax]
      exact htm
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp htrad
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hn

    have ht0' : ((t : ↥B) : K₁) ≠ 0 := fun h => ht0 (Subtype.ext h)
    have hs0' : ((s : ↥B) : K₁) ≠ 0 := fun h => hs0 (Subtype.ext h)
    have hsinv : ((s : ↥B) : K₁)⁻¹ = (c : K₁) * (((t : ↥B) : K₁)⁻¹) ^ n := by
      have hc' : (c : K₁) * (s : K₁) = ((t : ↥B) : K₁) ^ n := by
        have := congrArg (fun z : ↥B => (z : K₁)) hc
        simpa using this
      have hc0 : (c : K₁) ≠ 0 := by
        intro h
        rw [h, zero_mul] at hc'
        exact pow_ne_zero n ht0' hc'.symm
      rw [inv_pow, ← hc', mul_inv, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have hmem : ((s : ↥B) : K₁)⁻¹ ∈ O := by
      rw [hsinv]
      exact O.mul_mem _ _ (hBO _ c.2) (pow_mem hti n)
    have : (algebraMap ↥B K₁ b) / (algebraMap ↥B K₁ s) = (b : K₁) * ((s : ↥B) : K₁)⁻¹ := by
      rw [div_eq_mul_inv]; rfl
    rw [this]
    exact O.mul_mem _ _ (hBO _ b.2) hmem

  have hnf : ¬ IsField ↥B := by
    intro hF
    apply hO
    ext y
    refine ⟨fun _ => ValuationSubring.mem_top y, fun _ => ?_⟩
    obtain ⟨b, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := ↥B) y
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨s', hs'⟩ := hF.mul_inv_cancel hs0
    have : (algebraMap ↥B K₁ b) / (algebraMap ↥B K₁ s) = ((b * s' : ↥B) : K₁) := by
      have h1 : (s : K₁) * (s' : K₁) = 1 := by
        have := congrArg (fun z : ↥B => (z : K₁)) hs'
        simpa using this
      have hs0' : ((s : ↥B) : K₁) ≠ 0 := fun h => hs0 (Subtype.ext h)
      change (b : K₁) / (s : K₁) = ((b * s' : ↥B) : K₁)
      rw [div_eq_iff hs0']
      push_cast
      rw [mul_assoc, mul_comm (s' : K₁) (s : K₁), h1, mul_one]
    rw [this]
    exact hBO _ (b * s').2

  have hval : ValuationRing ↥B := by
    haveI : IsDedekindRing ↥B := IsDedekindRing.mk
    haveI : IsDedekindDomain ↥B := IsDedekindDomain.mk
    exact ((IsDiscreteValuationRing.TFAE ↥B hnf).out 2 1).mp ‹IsDedekindDomain ↥B›

  by_contra hxB
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxB isIntegral_zero
  rcases (ValuationRing.iff_isInteger_or_isInteger ↥B K₁).mp hval x with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact hxB ((hmemB x).mp (ht ▸ t.2))
  · have ht' : (t : K₁) = x⁻¹ := ht
    have ht0 : t ≠ 0 := by
      intro h
      rw [h] at ht'
      exact inv_ne_zero hx0 (by simpa using ht'.symm)
    have htm : t ∈ maximalIdeal ↥B := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨t', htt'⟩ := isUnit_iff_exists_inv.mp hu
      apply hxB
      rw [← hmemB]
      have : x = (t' : K₁) := by
        have h1 : (t : K₁) * (t' : K₁) = 1 := by
          have := congrArg (fun z : ↥B => (z : K₁)) htt'
          simpa using this
        rw [ht'] at h1
        calc x = x * (x⁻¹ * (t' : K₁)) := by rw [h1, mul_one]
          _ = (t' : K₁) := by rw [← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
      rw [this]
      exact t'.2
    refine key t ht0 htm ?_
    rw [ht', inv_inv]
    exact hx

theorem isIntegral_of_mem {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L)
    [HenselianLocalRing ↥(A.comap (algebraMap K L))] [IsDiscreteValuationRing ↥(A.comap (algebraMap K L))]
    (y : L) (hy : y ∈ A) :
    letI : Algebra ↥(A.comap (algebraMap K L)) L :=
      ((algebraMap K L).comp (A.comap (algebraMap K L)).subtype).toAlgebra
    IsIntegral ↥(A.comap (algebraMap K L)) y := by
  letI algL : Algebra ↥(A.comap (algebraMap K L)) L :=
    ((algebraMap K L).comp (A.comap (algebraMap K L)).subtype).toAlgebra
  haveI hKL : IsScalarTower ↥(A.comap (algebraMap K L)) K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hKyL : IsScalarTower ↥(A.comap (algebraMap K L)) ↥(IntermediateField.adjoin K {y}) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  haveI : Ring.KrullDimLE 1 ↥(A.comap (algebraMap K L)) :=
    Ring.KrullDimLE.mk₁' (fun I hI hp => hp.isMaximal hI)

  have hyint : IsIntegral K y := (Algebra.IsAlgebraic.isAlgebraic (R := K) y).isIntegral
  haveI : FiniteDimensional K ↥(IntermediateField.adjoin K {y}) := IntermediateField.adjoin.finiteDimensional hyint

  set O : ValuationSubring ↥(IntermediateField.adjoin K {y}) :=
    A.comap (algebraMap ↥(IntermediateField.adjoin K {y}) L) with hO_def
  have hA₀ : ∀ a : ↥(A.comap (algebraMap K L)),
      algebraMap ↥(A.comap (algebraMap K L)) ↥(IntermediateField.adjoin K {y}) a ∈ O := by
    intro a
    rw [hO_def, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact (ValuationSubring.mem_comap).mp a.2
  have hO : O ≠ ⊤ := by
    intro htop
    apply IsDiscreteValuationRing.not_a_field ↥(A.comap (algebraMap K L))

    have hall : ∀ k : K, algebraMap K L k ∈ A := fun k => by
      have h1 : algebraMap K ↥(IntermediateField.adjoin K {y}) k ∈ O := by
        rw [htop]; exact ValuationSubring.mem_top _
      rw [hO_def, ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply] at h1
      exact h1
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_bot]
    by_contra h0
    have ha0 : (a : K) ≠ 0 := fun h => h0 (Subtype.ext h)
    apply (IsLocalRing.mem_maximalIdeal _).mp ha
    refine isUnit_iff_exists_inv.mpr ⟨⟨(a : K)⁻¹, ?_⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩
    rw [ValuationSubring.mem_comap, map_inv₀]
    rw [← map_inv₀]
    exact hall _
  have hyO : (⟨y, IntermediateField.mem_adjoin_simple_self K y⟩ : ↥(IntermediateField.adjoin K {y})) ∈ O := by
    rw [hO_def, ValuationSubring.mem_comap]
    exact hy
  have hint := isIntegral_of_mem_valuationSubring (A₀ := ↥(A.comap (algebraMap K L))) (K₀ := K)
    (K₁ := ↥(IntermediateField.adjoin K {y})) O hA₀ hO _ hyO
  exact hint.map (IsScalarTower.toAlgHom ↥(A.comap (algebraMap K L)) ↥(IntermediateField.adjoin K {y}) L)

end ProlongIntAux

open IsLocalRing in

theorem solution
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L)
    [HenselianLocalRing ↥(A.comap (algebraMap K L))] [IsDiscreteValuationRing ↥(A.comap (algebraMap K L))]
    [Algebra ↥(A.comap (algebraMap K L)) ↥A]
    (halg : ∀ x : ↥(A.comap (algebraMap K L)),
      ((algebraMap ↥(A.comap (algebraMap K L)) ↥A x : ↥A) : L) = algebraMap K L (x : K)) :
    Module.FaithfullyFlat ↥(A.comap (algebraMap K L)) ↥A ∧
      Algebra.IsIntegral ↥(A.comap (algebraMap K L)) ↥A := by
  letI algL : Algebra ↥(A.comap (algebraMap K L)) L :=
    ((algebraMap K L).comp (A.comap (algebraMap K L)).subtype).toAlgebra
  haveI hKL : IsScalarTower ↥(A.comap (algebraMap K L)) K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hAL : IsScalarTower ↥(A.comap (algebraMap K L)) ↥A L :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      symm
      exact halg x)
  have hinj : Function.Injective (algebraMap ↥(A.comap (algebraMap K L)) ↥A) := by
    intro x y h
    have h' := congrArg (fun z : ↥A => (z : L)) h
    simp only [halg] at h'
    exact Subtype.ext ((algebraMap K L).injective h')
  refine ⟨?_, ⟨fun a => ?_⟩⟩
  ·
    haveI : Module.IsTorsionFree ↥(A.comap (algebraMap K L)) ↥A :=
      (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
    haveI : Module.Flat ↥(A.comap (algebraMap K L)) ↥A := inferInstance
    haveI : IsLocalHom (algebraMap ↥(A.comap (algebraMap K L)) ↥A) := by
      refine ⟨fun x hx => ?_⟩
      obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hx
      have h1 : algebraMap K L (x : K) * (y : L) = 1 := by
        have := congrArg (fun z : ↥A => (z : L)) hy
        simpa [halg] using this
      have hx0 : (x : K) ≠ 0 := by
        intro h0
        rw [h0, map_zero, zero_mul] at h1
        exact zero_ne_one h1
      have hyL : (y : L) = algebraMap K L ((x : K)⁻¹) := by
        rw [map_inv₀]
        exact eq_inv_of_mul_eq_one_right h1
      have hinv : (x : K)⁻¹ ∈ A.comap (algebraMap K L) := by
        rw [ValuationSubring.mem_comap, ← hyL]
        exact y.2
      exact isUnit_iff_exists_inv.mpr ⟨⟨(x : K)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩
    exact Module.FaithfullyFlat.of_flat_of_isLocalHom
  ·
    exact IsIntegral.tower_bot (A := ↥A) (B := L) Subtype.val_injective
      (ProlongIntAux.isIntegral_of_mem A (a : L) a.2)

end S_ValuationSubring_faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap
end P2MW
export P2MW.S_ValuationSubring_faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap (solution)
