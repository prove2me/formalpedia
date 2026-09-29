-- Prove2me | solution 1 for ValuationSubring.mem_adjoin_singleton_of_isIntegral_of_separable_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/59d500da-48e0-52ae-9fe7-7d6a7be3bd03

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_separable_minpoly

set_option autoImplicit false

open Polynomial

namespace Ws50V1

section RootDiff

variable {κ E : Type*} [Field κ] [Field E] [Algebra κ E] (B : ValuationSubring E)

theorem integers : B.valuation.Integers B where
  hom_inj := Subtype.val_injective
  map_le_one := B.valuation_le_one
  exists_of_le_one := fun x hx => ⟨⟨x, (B.valuation_le_one_iff x).mp hx⟩, rfl⟩

theorem mem_of_isIntegral (hκ : ∀ a : κ, algebraMap κ E a ∈ B) {s : E} (hs : IsIntegral κ s) : s ∈ B := by
  let φ : κ →+* B := (algebraMap κ E).codRestrict B hκ
  have hφ : (algebraMap B E).comp φ = algebraMap κ E := RingHom.ext fun _ => rfl
  have hs' : IsIntegral B s := by
    obtain ⟨p, hp, hps⟩ := hs
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [eval₂_map, hφ]; exact hps
  have h := (integers B).mem_of_integral hs'
  rw [Valuation.mem_integer_iff] at h
  exact (B.valuation_le_one_iff s).mp h

theorem aeval_mem (hκ : ∀ a : κ, algebraMap κ E a ∈ B) (q : κ[X]) {s : E} (hs : s ∈ B) : aeval s q ∈ B := by
  let S : Subalgebra κ E :=
    { B.toSubring.toSubsemiring with
      algebraMap_mem' := hκ }
  have hS : ∀ x, x ∈ S ↔ x ∈ B := fun x => Iff.rfl
  have h1 : Algebra.adjoin κ {s} ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.mpr ((hS s).mpr hs))
  exact (hS _).mp (h1 (aeval_mem_adjoin_singleton κ s))

theorem eq_one_of_prod_map_eq_one {ι M : Type*} [CommMonoid M] [PartialOrder M] [IsOrderedMonoid M] [DecidableEq ι]
    (s : Multiset ι) (f : ι → M) (hle : ∀ a ∈ s, f a ≤ 1) (hprod : (s.map f).prod = 1) {a : ι} (ha : a ∈ s) :
    f a = 1 := by
  have key := Multiset.prod_map_erase (f := f) ha
  rw [hprod] at key
  have hP : ((s.erase a).map f).prod ≤ 1 := by
    have h := Multiset.prod_le_pow_card ((s.erase a).map f) 1 fun x hx => by
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp hx
      exact hle b (Multiset.mem_of_mem_erase hb)
    rwa [one_pow] at h
  apply le_antisymm (hle a ha)
  calc 1 = f a * ((s.erase a).map f).prod := key.symm
    _ ≤ f a * 1 := mul_le_mul_right hP _
    _ = f a := mul_one _

theorem valuation_sub_eq_one (hκ : ∀ a : κ, algebraMap κ E a ∈ B)
    {g : κ[X]} (hg : g.Monic) (hsep : g.Separable) (hsplit : (g.map (algebraMap κ E)).Splits)
    {r r' : E} (hr : r ∈ (g.map (algebraMap κ E)).roots) (hr' : r' ∈ (g.map (algebraMap κ E)).roots)
    (hne : r ≠ r') : B.valuation (r - r') = 1 := by
  classical
  set G := g.map (algebraMap κ E) with hG
  have hGm : G.Monic := hg.map _
  have root_mem : ∀ s ∈ G.roots, s ∈ B := fun s hs =>
    mem_of_isIntegral B hκ ⟨g, hg, by
      have h := (mem_roots hGm.ne_zero).mp hs
      rwa [IsRoot.def, eval_map] at h⟩

  obtain ⟨a, b, hab⟩ := hsep
  have hgr : aeval r g = 0 := by
    have h := (mem_roots hGm.ne_zero).mp hr
    rwa [IsRoot.def, eval_map, ← aeval_def] at h
  have hunit : aeval r b * aeval r (derivative g) = 1 := by
    have h := congrArg (aeval r) hab
    rwa [map_add, map_mul, map_mul, hgr, mul_zero, zero_add, map_one] at h

  have hder : aeval r (derivative g) = ((G.roots.erase r).map (r - ·)).prod := by
    rw [aeval_def, ← eval_map, ← derivative_map]
    exact hsplit.eval_root_derivative hGm hr
  have hvb : B.valuation (aeval r b) ≤ 1 := (B.valuation_le_one_iff _).mpr (aeval_mem B hκ b (root_mem r hr))
  have hvd : B.valuation (aeval r (derivative g)) ≤ 1 :=
    (B.valuation_le_one_iff _).mpr (aeval_mem B hκ _ (root_mem r hr))
  have hvd1 : B.valuation (aeval r (derivative g)) = 1 := by
    have h := congrArg B.valuation hunit
    rw [map_mul, map_one] at h
    apply le_antisymm hvd
    calc 1 = B.valuation (aeval r b) * B.valuation (aeval r (derivative g)) := h.symm
      _ ≤ 1 * B.valuation (aeval r (derivative g)) := mul_le_mul_left hvb _
      _ = _ := one_mul _
  rw [hder, map_multiset_prod, Multiset.map_map] at hvd1
  have hle : ∀ x ∈ G.roots.erase r, (B.valuation ∘ fun y => r - y) x ≤ 1 := fun x hx =>
    (B.valuation_le_one_iff _).mpr (B.sub_mem (root_mem r hr) (root_mem x (Multiset.mem_of_mem_erase hx)))
  have hmem : r' ∈ G.roots.erase r := (Multiset.mem_erase_of_ne hne.symm).mpr hr'
  exact eq_one_of_prod_map_eq_one (G.roots.erase r) (B.valuation ∘ fun y => r - y) hle hvd1 hmem

end RootDiff

section Main

variable {κ F L : Type*} [Field κ] [Field F] [Field L] [Algebra κ F] [Algebra F L] [Algebra κ L]
  [IsScalarTower κ F L] (𝒪 : ValuationSubring F) [Algebra 𝒪 L] [IsScalarTower 𝒪 F L]

theorem exists_unit_eq_discr (hκ : ∀ a : κ, algebraMap κ F a ∈ 𝒪)
    (c : L) (hc : IsIntegral κ c) (hsep : (minpoly κ c).Separable)
    (pb : PowerBasis F L) (hpb : pb.gen = c) [FiniteDimensional F L] [Algebra.IsSeparable F L] :
    ∃ u : 𝒪ˣ, algebraMap 𝒪 F u = Algebra.discr F pb.basis := by
  classical
  let E := AlgebraicClosure L

  haveI : IsScalarTower κ F E := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply κ L E, IsScalarTower.algebraMap_apply κ F L,
      ← IsScalarTower.algebraMap_apply F L E]

  let f : 𝒪 →+* E := (algebraMap L E).comp (algebraMap 𝒪 L)
  have hf : ∀ x : 𝒪, f x = algebraMap F E x := fun x => by
    show algebraMap L E (algebraMap 𝒪 L x) = _
    rw [IsScalarTower.algebraMap_apply 𝒪 F L, ← IsScalarTower.algebraMap_apply F L E]
    rfl
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have hκE : ∀ a : κ, algebraMap κ E a ∈ B := fun a => by
    have h := hB ⟨algebraMap κ F a, hκ a⟩
    rw [hf] at h
    rw [IsScalarTower.algebraMap_apply κ F E]
    exact h

  have eqv : Fin pb.dim ≃ (L →ₐ[F] E) := by
    refine Fintype.equivOfCardEq ?_
    rw [Fintype.card_fin, AlgHom.card]
    exact pb.finrank.symm

  have hprod := Algebra.discr_powerBasis_eq_prod F E pb eqv

  set g := minpoly κ c with hg
  set G := g.map (algebraMap κ E) with hG
  have hgm : g.Monic := minpoly.monic hc
  have hGm : G.Monic := hgm.map _
  have hroot : ∀ σ : L →ₐ[F] E, σ pb.gen ∈ G.roots := fun σ => by
    rw [mem_roots hGm.ne_zero, IsRoot.def, eval_map, ← aeval_def, hpb]
    have h1 : aeval (σ c) g = aeval (σ c) (g.map (algebraMap κ F)) := (aeval_map_algebraMap F (σ c) g).symm
    rw [h1, aeval_algHom_apply, aeval_map_algebraMap, hg, minpoly.aeval, map_zero]
  have hdiff : ∀ i j : Fin pb.dim, i ≠ j → B.valuation (eqv j pb.gen - eqv i pb.gen) = 1 := by
    intro i j hij
    refine valuation_sub_eq_one B hκE hgm hsep (IsAlgClosed.splits G) (hroot _) (hroot _) fun h => hij ?_
    exact (eqv.injective (pb.algHom_ext h)).symm
  have hv1 : B.valuation (algebraMap F E (Algebra.discr F pb.basis)) = 1 := by
    rw [hprod, map_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [map_prod]
    refine Finset.prod_eq_one fun j hj => ?_
    rw [map_pow, hdiff i j (Finset.mem_Ioi.mp hj).ne, one_pow]

  have unit_of : ∀ x : 𝒪, B.valuation (algebraMap F E x) = 1 → IsUnit x := by
    intro x hx
    refine hloc.1 x ?_
    rw [ValuationSubring.valuation_eq_one_iff]
    show B.valuation (f x) = 1
    rwa [hf]
  set d := Algebra.discr F pb.basis with hd
  rcases 𝒪.mem_or_inv_mem d with hmem | hmem
  · obtain ⟨u, hu⟩ := unit_of ⟨d, hmem⟩ hv1
    exact ⟨u, by rw [hu]; rfl⟩
  · have hv1' : B.valuation (algebraMap F E ((⟨d⁻¹, hmem⟩ : 𝒪) : F)) = 1 := by
      show B.valuation (algebraMap F E d⁻¹) = 1
      rw [map_inv₀, map_inv₀, hv1, inv_one]
    obtain ⟨u, hu⟩ := unit_of ⟨d⁻¹, hmem⟩ hv1'
    refine ⟨u⁻¹, ?_⟩
    have h1 : (algebraMap 𝒪 F u) * (algebraMap 𝒪 F ↑u⁻¹) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 : algebraMap 𝒪 F u = d⁻¹ := by rw [hu]; rfl
    rw [h2] at h1
    have hd0 : d ≠ 0 := by
      intro h0
      rw [h0, inv_zero, zero_mul] at h1
      exact zero_ne_one h1
    calc algebraMap 𝒪 F ↑u⁻¹ = d * (d⁻¹ * algebraMap 𝒪 F ↑u⁻¹) := by
          rw [← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
      _ = d := by rw [h1, mul_one]

end Main

end Ws50V1

open Ws50V1 in

theorem solution
    {κ F L : Type*} [Field κ] [Field F] [Field L] [Algebra κ F] [Algebra F L] [Algebra κ L] [IsScalarTower κ F L]
    (𝒪 : ValuationSubring F) [Algebra 𝒪 L] [IsScalarTower 𝒪 F L]
    (hκ : ∀ a : κ, algebraMap κ F a ∈ 𝒪)
    (c : L) (hc : IsIntegral κ c) (hsep : (minpoly κ c).Separable)
    (hgen : IntermediateField.adjoin F ({c} : Set L) = ⊤)
    (z : L) (hz : IsIntegral 𝒪 z) :
    z ∈ Algebra.adjoin 𝒪 ({c} : Set L) := by
  classical
  have hcF : IsIntegral F c := hc.tower_top

  let e : IntermediateField.adjoin F ({c} : Set L) ≃ₐ[F] L :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  let pb : PowerBasis F L := (IntermediateField.adjoin.powerBasis hcF).map e
  have hpb : pb.gen = c := by
    show e (IntermediateField.adjoin.powerBasis hcF).gen = c
    rw [IntermediateField.adjoin.powerBasis_gen]
    rfl
  haveI : FiniteDimensional F L := PowerBasis.finite pb
  haveI : Algebra.IsSeparable F L := by
    have hsc : IsSeparable F c := IsSeparable.tower_top F (show IsSeparable κ c from hsep)
    haveI := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F L).mpr hsc
    exact AlgEquiv.Algebra.isSeparable e

  have hcO : IsIntegral 𝒪 c := by
    let φ : κ →+* 𝒪 := (algebraMap κ F).codRestrict 𝒪 hκ
    have hφ : (algebraMap 𝒪 L).comp φ = algebraMap κ L := by
      ext a
      show algebraMap 𝒪 L (φ a) = algebraMap κ L a
      rw [IsScalarTower.algebraMap_apply 𝒪 F L, IsScalarTower.algebraMap_apply κ F L]
      rfl
    obtain ⟨p, hp, hps⟩ := id hc
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [eval₂_map, hφ]; exact hps

  have hmem := Algebra.discr_mul_isIntegral_mem_adjoin F (B := pb) (by rw [hpb]; exact hcO) hz
  rw [hpb] at hmem

  obtain ⟨u, hu⟩ := exists_unit_eq_discr 𝒪 hκ c hc hsep pb hpb
  have key : z = algebraMap 𝒪 L ↑u⁻¹ * (Algebra.discr F pb.basis • z) := by
    rw [Algebra.smul_def, ← hu, ← IsScalarTower.algebraMap_apply 𝒪 F L, ← mul_assoc, ← map_mul, Units.inv_mul,
      map_one, one_mul]
  rw [key]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hmem

end S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_separable_minpoly
end P2MW
export P2MW.S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_separable_minpoly (solution)
