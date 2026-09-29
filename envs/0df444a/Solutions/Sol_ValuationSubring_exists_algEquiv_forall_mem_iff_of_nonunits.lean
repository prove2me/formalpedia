-- Prove2me | solution 1 for ValuationSubring.exists_algEquiv_forall_mem_iff_of_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/9cfa9f5e-8ff1-5c0b-8344-96a91aa5ea3c

import Mathlib
import Theorems.Thm_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_nonunits

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open NumberField IsDedekindDomain

namespace P2mWs11L8

theorem mem_nonunits_iff' {F : Type*} [Field F] (A : ValuationSubring F) (x : F) :
    x ∈ A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rw [ValuationSubring.mem_nonunits_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp only [hx, false_or]
    rw [← ValuationSubring.valuation_le_one_iff, not_le, Valuation.one_lt_val_iff _ (inv_ne_zero hx),
      inv_inv]

theorem mem_nonunits_comap {F E : Type*} [Field F] [Field E] (A : ValuationSubring E) (f : F →+* E)
    (x : F) : x ∈ (A.comap f).nonunits ↔ f x ∈ A.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_comap, map_inv₀,
    map_eq_zero_iff f f.injective]

theorem mem_of_isIntegral_int (A : ValuationSubring (AlgebraicClosure ℚ)) {x : AlgebraicClosure ℚ}
    (hx : IsIntegral ℤ x) : x ∈ A := by
  have hxA : IsIntegral A x := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (Int.castRingHom A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap A (AlgebraicClosure ℚ)).comp (Int.castRingHom A))
      (algebraMap ℤ (AlgebraicClosure ℚ))]
    exact hpx
  obtain ⟨y, hy⟩ :=
    (IsIntegrallyClosed.isIntegral_iff (R := A) (K := AlgebraicClosure ℚ)).mp hxA
  rw [← hy]
  exact y.2

theorem main (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A A'' : ValuationSubring (AlgebraicClosure ℚ))
    (hle : ∀ x : AlgebraicClosure ℚ, x ∈ K → x ∈ A → x ∈ A'')
    {q : ℕ} (hq : q.Prime)
    (hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (hqA'' : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A''.nonunits)
    (L : IntermediateField ↥K (AlgebraicClosure ℚ)) [FiniteDimensional ↥K L] :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ,
      ∀ x : AlgebraicClosure ℚ, x ∈ L → (x ∈ A'' ↔ τ x ∈ A) := by
  classical
  haveI : NumberField K := ⟨⟩

  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal K (AlgebraicClosure ℚ) := IsAlgClosure.normal K (AlgebraicClosure ℚ)
  let M : IntermediateField K (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure K L (AlgebraicClosure ℚ)
  have hLM : L ≤ M := IntermediateField.le_normalClosure L
  haveI : FiniteDimensional K M := normalClosure.is_finiteDimensional K L (AlgebraicClosure ℚ)
  haveI : Normal K M := normalClosure.normal K L (AlgebraicClosure ℚ)
  haveI : IsGalois K M := ⟨⟩
  haveI : FiniteDimensional ℚ M := Module.Finite.trans K M
  haveI : NumberField M := ⟨⟩
  haveI : IsScalarTower (𝓞 K) M (AlgebraicClosure ℚ) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g : M →+* AlgebraicClosure ℚ := algebraMap M (AlgebraicClosure ℚ)
  have hg : ∀ x : M, g x = (x : AlgebraicClosure ℚ) := fun x => rfl

  have hint : ∀ s : 𝓞 M, IsIntegral ℤ (g (algebraMap (𝓞 M) M s)) := fun s => by
    obtain ⟨p, hp, h0⟩ := RingOfIntegers.isIntegral_coe s
    have h0' : Polynomial.eval₂ (algebraMap ℤ M) (algebraMap (𝓞 M) M s) p = 0 := h0
    refine ⟨p, hp, ?_⟩
    rw [← RingHom.ext_int (g.comp (algebraMap ℤ M)) (algebraMap ℤ (AlgebraicClosure ℚ)),
      ← Polynomial.hom_eval₂, h0', map_zero]
  have hRV : ∀ (B : ValuationSubring (AlgebraicClosure ℚ)) (s : 𝓞 M),
      (algebraMap (𝓞 M) M s : M) ∈ B.comap g := fun B s => by
    rw [ValuationSubring.mem_comap]
    exact mem_of_isIntegral_int B (hint s)
  have hne : ∀ B : ValuationSubring (AlgebraicClosure ℚ),
      ((q : ℕ) : AlgebraicClosure ℚ) ∈ B.nonunits → B.comap g ≠ ⊤ := by
    intro B hqB htop
    have h1 : ((q : M)⁻¹ : M) ∈ B.comap g := by rw [htop]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at h1
    rcases (mem_nonunits_iff' B _).mp hqB with h0 | h0
    · exact hq.ne_zero (by exact_mod_cast h0)
    · exact h0 h1

  obtain ⟨v₁, hV₁, hv₁⟩ :=
    ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem (A.comap g) (hRV A)
      (hne A hqA)
  obtain ⟨v₂, hV₂, hv₂⟩ :=
    ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem (A''.comap g) (hRV A'')
      (hne A'' hqA'')

  have hv₁' : ∀ s : 𝓞 M, s ∈ v₁.asIdeal ↔ g (algebraMap (𝓞 M) M s) ∈ A.nonunits := fun s => by
    rw [hv₁, mem_nonunits_comap]
  have hv₂' : ∀ s : 𝓞 M, s ∈ v₂.asIdeal ↔ g (algebraMap (𝓞 M) M s) ∈ A''.nonunits := fun s => by
    rw [hv₂, mem_nonunits_comap]
  have hOK : ∀ r : 𝓞 K, g (algebraMap (𝓞 M) M (algebraMap (𝓞 K) (𝓞 M) r)) =
      algebraMap (𝓞 K) (AlgebraicClosure ℚ) r := fun r => by
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M]
    rfl

  have hKle : A.comap (algebraMap K (AlgebraicClosure ℚ)) ≤ A''.comap (algebraMap K (AlgebraicClosure ℚ)) :=
    fun y hy => by
      rw [ValuationSubring.mem_comap] at hy ⊢
      exact hle _ y.2 hy
  have hKnon : ∀ y : K, (y : AlgebraicClosure ℚ) ∈ A''.nonunits → (y : AlgebraicClosure ℚ) ∈ A.nonunits := by
    intro y hy
    have := (ValuationSubring.nonunits_le_nonunits.mpr hKle)
      ((mem_nonunits_comap A'' (algebraMap K (AlgebraicClosure ℚ)) y).mpr hy)
    exact (mem_nonunits_comap A (algebraMap K (AlgebraicClosure ℚ)) y).mp this

  obtain ⟨p, hp⟩ : ∃ p : Ideal (𝓞 K), p = v₁.asIdeal.under (𝓞 K) := ⟨_, rfl⟩
  have hsub : v₂.asIdeal.under (𝓞 K) ≤ p := by
    intro r hr
    rw [hp, Ideal.under_def, Ideal.mem_comap, hv₁', hOK]
    rw [Ideal.under_def, Ideal.mem_comap, hv₂', hOK] at hr
    exact hKnon _ hr
  have hq₂ : ((q : ℕ) : 𝓞 K) ∈ v₂.asIdeal.under (𝓞 K) := by
    rw [Ideal.under_def, Ideal.mem_comap, hv₂', hOK, map_natCast]
    exact hqA''
  have hmax : (v₂.asIdeal.under (𝓞 K)).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun hbot => ?_
    rw [hbot, Ideal.mem_bot] at hq₂
    exact hq.ne_zero (by exact_mod_cast hq₂)
  have hp_ne : p ≠ ⊤ := by rw [hp]; exact Ideal.IsPrime.ne_top inferInstance
  have hunder : v₂.asIdeal.under (𝓞 K) = p := hmax.eq_of_le hp_ne hsub

  have hP₁ : v₁.asIdeal ∈ p.primesOver (𝓞 M) := ⟨v₁.isPrime, ⟨hp⟩⟩
  have hP₂ : v₂.asIdeal ∈ p.primesOver (𝓞 M) := ⟨v₂.isPrime, ⟨hunder.symm⟩⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 K) K M (𝓞 M) hP₁ hP₂

  let W : ValuationSubring M := A.comap (g.comp (σ : M →+* M))
  have hWint : ∀ s : 𝓞 M, (algebraMap (𝓞 M) M s : M) ∈ W := fun s => by
    rw [ValuationSubring.mem_comap, RingHom.comp_apply, RingHom.coe_coe,
      ← algebraMap_galRestrict_apply (𝓞 K)]
    exact mem_of_isIntegral_int A (hint _)
  have hWne : W ≠ ⊤ := by
    intro htop
    have h1 : ((q : M)⁻¹ : M) ∈ W := by rw [htop]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap, RingHom.comp_apply, RingHom.coe_coe, map_inv₀, map_natCast,
      map_inv₀, map_natCast] at h1
    rcases (mem_nonunits_iff' A _).mp hqA with h0 | h0
    · exact hq.ne_zero (by exact_mod_cast h0)
    · exact h0 h1
  obtain ⟨w, hW, hw⟩ :=
    ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem W hWint hWne
  have hwv : w = v₂ := by
    apply HeightOneSpectrum.ext
    ext s
    rw [hw, mem_nonunits_comap, RingHom.comp_apply, RingHom.coe_coe,
      ← algebraMap_galRestrict_apply (𝓞 K), ← mem_nonunits_comap, ← hv₁, ← Ideal.mem_comap]
    show s ∈ Ideal.comap ((galRestrict (𝓞 K) K M (𝓞 M)) σ) v₁.asIdeal ↔ s ∈ v₂.asIdeal
    rw [hσ]

  have hM : ∀ x : M, (x : AlgebraicClosure ℚ) ∈ A'' ↔ ((σ x : M) : AlgebraicClosure ℚ) ∈ A := by
    intro x
    have h1 : x ∈ A''.comap g ↔ x ∈ W := by rw [hV₂, hW, hwv]
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at h1
    exact h1

  refine ⟨AlgEquiv.liftNormal σ (AlgebraicClosure ℚ), fun x hx => ?_⟩
  have key := hM ⟨x, hLM hx⟩
  have hτ : AlgEquiv.liftNormal σ (AlgebraicClosure ℚ) x =
      ((σ ⟨x, hLM hx⟩ : M) : AlgebraicClosure ℚ) :=
    AlgEquiv.liftNormal_commutes σ (AlgebraicClosure ℚ) ⟨x, hLM hx⟩
  rw [hτ]
  exact key

end P2mWs11L8

theorem solution
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A A'' : ValuationSubring (AlgebraicClosure ℚ))
    (hle : ∀ x : AlgebraicClosure ℚ, x ∈ K → x ∈ A → x ∈ A'')
    {q : ℕ} (hq : q.Prime)
    (hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits) (hqA'' : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A''.nonunits)
    (L : IntermediateField ↥K (AlgebraicClosure ℚ)) [FiniteDimensional ↥K L] :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[↥K] AlgebraicClosure ℚ,
      ∀ x : AlgebraicClosure ℚ, x ∈ L → (x ∈ A'' ↔ τ x ∈ A) :=
  P2mWs11L8.main K A A'' hle hq hqA hqA'' L

end S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_nonunits
end P2MW
export P2MW.S_ValuationSubring_exists_algEquiv_forall_mem_iff_of_nonunits (solution)
