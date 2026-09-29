-- Prove2me | solution 1 for ValuationSubring.finite_range_residue_of_nonunits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/06fcd7af-644f-5e1f-bdf1-f040501c323e

import Mathlib
import Theorems.Thm_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_finite_range_residue_of_nonunits

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open NumberField IsDedekindDomain

namespace P2mWs11NT

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

theorem exists_eq_mul_inv_of_mem_valuationSubringAtPrime {R F : Type*} [CommRing R] [IsDedekindDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] (v : HeightOneSpectrum R) (x : F)
    (hx : x ∈ v.valuationSubringAtPrime F) :
    ∃ a s : R, s ∉ v.asIdeal ∧ x = algebraMap R F a * (algebraMap R F s)⁻¹ := by
  unfold HeightOneSpectrum.valuationSubringAtPrime at hx
  rw [ValuationSubring.mem_ofSubring, Subalgebra.mem_toSubring] at hx
  unfold Localization.subalgebra.ofField at hx
  obtain ⟨a, s, hs, h⟩ :
      ∃ a s : R, ∃ (_ : s ∈ v.asIdeal.primeCompl), x = algebraMap R F a * (algebraMap R F s)⁻¹ := hx
  exact ⟨a, s, hs, h⟩

theorem residue_eq_zero_iff_mem_nonunits (A : ValuationSubring (AlgebraicClosure ℚ)) (x : A) :
    IsLocalRing.residue A x = 0 ↔ (x : AlgebraicClosure ℚ) ∈ A.nonunits := by
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  simp

theorem main (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    (hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (L : IntermediateField ↥K (AlgebraicClosure ℚ)) [FiniteDimensional ↥K L] :
    (Set.range fun x : {x : AlgebraicClosure ℚ // x ∈ L ∧ x ∈ A} =>
      IsLocalRing.residue ↥A ⟨x.1, x.2.2⟩).Finite := by
  classical
  haveI : NumberField K := ⟨⟩
  haveI : FiniteDimensional ℚ L := Module.Finite.trans K L
  haveI : NumberField L := ⟨⟩
  let g : L →+* AlgebraicClosure ℚ := algebraMap L (AlgebraicClosure ℚ)
  have hg : ∀ x : L, g x = (x : AlgebraicClosure ℚ) := fun x => rfl

  have hint : ∀ s : 𝓞 L, IsIntegral ℤ (g (algebraMap (𝓞 L) L s)) := fun s => by
    obtain ⟨p, hp, h0⟩ := RingOfIntegers.isIntegral_coe s
    have h0' : Polynomial.eval₂ (algebraMap ℤ L) (algebraMap (𝓞 L) L s) p = 0 := h0
    refine ⟨p, hp, ?_⟩
    rw [← RingHom.ext_int (g.comp (algebraMap ℤ L)) (algebraMap ℤ (AlgebraicClosure ℚ)),
      ← Polynomial.hom_eval₂, h0', map_zero]
  have hmemA : ∀ s : 𝓞 L, g (algebraMap (𝓞 L) L s) ∈ A := fun s => mem_of_isIntegral_int A (hint s)
  have hRV : ∀ s : 𝓞 L, (algebraMap (𝓞 L) L s : L) ∈ A.comap g := fun s => by
    rw [ValuationSubring.mem_comap]; exact hmemA s
  have hne : A.comap g ≠ ⊤ := by
    intro htop
    have h1 : ((q : L)⁻¹ : L) ∈ A.comap g := by rw [htop]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at h1
    rcases (mem_nonunits_iff' A _).mp hqA with h0 | h0
    · exact hq.ne_zero (by exact_mod_cast h0)
    · exact h0 h1
  obtain ⟨v, hV, hv⟩ :=
    ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem (A.comap g) hRV hne
  have hv' : ∀ s : 𝓞 L, s ∈ v.asIdeal ↔ g (algebraMap (𝓞 L) L s) ∈ A.nonunits := fun s => by
    rw [hv, mem_nonunits_comap]

  let r : 𝓞 L → IsLocalRing.ResidueField A := fun y =>
    IsLocalRing.residue A ⟨g (algebraMap (𝓞 L) L y), hmemA y⟩
  have hr : ∀ y y' : 𝓞 L, y - y' ∈ v.asIdeal → r y = r y' := by
    intro y y' h
    rw [← sub_eq_zero]
    simp only [r]
    rw [← map_sub, residue_eq_zero_iff_mem_nonunits]
    have : ((⟨g (algebraMap (𝓞 L) L y), hmemA y⟩ - ⟨g (algebraMap (𝓞 L) L y'), hmemA y'⟩ : A) :
        AlgebraicClosure ℚ) = g (algebraMap (𝓞 L) L (y - y')) := by
      simp
    rw [this, ← hv']
    exact h
  haveI : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let S : Set (IsLocalRing.ResidueField A) := Set.range fun c : 𝓞 L ⧸ v.asIdeal => r c.out
  have hSfin : S.Finite := Set.finite_range _
  have hrS : ∀ y : 𝓞 L, r y ∈ S := by
    intro y
    refine ⟨Ideal.Quotient.mk v.asIdeal y, hr _ _ ?_⟩
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]

  refine (hSfin.image2 (fun a b => a * b⁻¹) hSfin).subset ?_
  rintro _ ⟨⟨x, hxL, hxA⟩, rfl⟩
  have hxV : (⟨x, hxL⟩ : L) ∈ A.comap g := by rw [ValuationSubring.mem_comap]; exact hxA
  rw [hV] at hxV
  obtain ⟨a, s, hs, hxas⟩ := exists_eq_mul_inv_of_mem_valuationSubringAtPrime v _ hxV
  have hx' : x = g (algebraMap (𝓞 L) L a) * (g (algebraMap (𝓞 L) L s))⁻¹ := by
    have := congrArg g hxas
    rwa [map_mul, map_inv₀] at this
  have hs0 : IsLocalRing.residue A ⟨g (algebraMap (𝓞 L) L s), hmemA s⟩ ≠ 0 := by
    rw [Ne, residue_eq_zero_iff_mem_nonunits, ← hv']
    exact hs
  have hsne : g (algebraMap (𝓞 L) L s) ≠ 0 := by
    intro h0
    apply hs0
    rw [residue_eq_zero_iff_mem_nonunits]
    simp only [h0]
    exact (mem_nonunits_iff' A 0).mpr (Or.inl rfl)
  refine ⟨r a, hrS a, r s, hrS s, ?_⟩
  simp only [r]
  symm
  rw [eq_mul_inv_iff_mul_eq₀ hs0, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [MulMemClass.coe_mul]
  rw [hx', inv_mul_cancel_right₀ hsne]

end P2mWs11NT

theorem solution
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    (hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (L : IntermediateField ↥K (AlgebraicClosure ℚ)) [FiniteDimensional ↥K L] :
    (Set.range fun x : {x : AlgebraicClosure ℚ // x ∈ L ∧ x ∈ A} =>
      IsLocalRing.residue ↥A ⟨x.1, x.2.2⟩).Finite :=
  P2mWs11NT.main K A hq hqA L

end S_ValuationSubring_finite_range_residue_of_nonunits
end P2MW
export P2MW.S_ValuationSubring_finite_range_residue_of_nonunits (solution)
