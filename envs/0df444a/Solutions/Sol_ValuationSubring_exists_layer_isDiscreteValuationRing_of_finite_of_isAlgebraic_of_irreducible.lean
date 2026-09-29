-- Prove2me | solution 1 for ValuationSubring.exists_layer_isDiscreteValuationRing_of_finite_of_isAlgebraic_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/43fec992-3519-51bd-aac7-5655303a23b0

import Mathlib
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_layer_isDiscreteValuationRing_of_finite_of_isAlgebraic_of_irreducible

set_option autoImplicit false
open IsLocalRing

namespace BDescL1

theorem mem_of_isIntegral {L : Type} [Field L] (A : ValuationSubring L) {x : L} (hx : IsIntegral ↥A x) : x ∈ A := by
  have hAint : A.valuation.Integers ↥A :=
    { hom_inj := Subtype.coe_injective
      map_le_one := fun a => (A.valuation_le_one_iff (a : L)).mpr a.2
      exists_of_le_one := fun r hr => ⟨⟨r, (A.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
  have := hAint.mem_of_integral hx
  exact (A.valuation_le_one_iff x).mp ((Valuation.mem_integer_iff _ _).mp this)

theorem mem_maximalIdeal_iff_inv_not_mem {L : Type} [Field L] (A : ValuationSubring L) (x : L) (hx : x ∈ A) (hx0 : x ≠ 0) :
    (⟨x, hx⟩ : ↥A) ∈ maximalIdeal ↥A ↔ x⁻¹ ∉ A := by
  rw [ValuationSubring.valuation_lt_one_iff, ← A.valuation_le_one_iff, map_inv₀, not_le]
  show A.valuation x < 1 ↔ 1 < (A.valuation x)⁻¹
  rw [one_lt_inv₀ (((map_ne_zero A.valuation).mpr hx0).bot_lt)]

theorem residue_eq_zero_iff_inv_not_mem {L : Type} [Field L] (A : ValuationSubring L) (x : L) (hx : x ∈ A) (hx0 : x ≠ 0) :
    IsLocalRing.residue ↥A ⟨x, hx⟩ = 0 ↔ x⁻¹ ∉ A := by
  rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff_inv_not_mem A x hx hx0]

theorem isUnit_of_inv_mem {L : Type} [Field L] (B : Subring L) (x : L) (hx : x ∈ B) (hxi : x⁻¹ ∈ B) (hx0 : x ≠ 0) :
    IsUnit (⟨x, hx⟩ : ↥B) :=
  ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hxi⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem inv_mem_of_isUnit {L : Type} [Field L] (B : Subring L) (x : ↥B) (hx : IsUnit x) : ((x : L))⁻¹ ∈ B := by
  obtain ⟨u, rfl⟩ := hx
  have h : ((u : ↥B) : L) * (((u⁻¹ : (↥B)ˣ) : ↥B) : L) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rw [inv_eq_of_mul_eq_one_right h]
  exact ((u⁻¹ : (↥B)ˣ) : ↥B).2

end BDescL1

namespace GenLoc

open IsLocalRing

theorem exists_frac_unit_of_mem_valuationSubring
    {B : Type} [CommRing B] [IsDedekindDomain B]
    {E : Type} [Field E] [Algebra B E] [IsFractionRing B E]
    (V : ValuationSubring E) (hBV : ∀ b : B, algebraMap B E b ∈ V) (hV : V ≠ ⊤)
    (c : E) (hc : c ∈ V) :
    ∃ b s : B, s ≠ 0 ∧ algebraMap B E s ∉ V.nonunits ∧ c * algebraMap B E s = algebraMap B E b := by
  classical
  have hinj : Function.Injective (algebraMap B E) := IsFractionRing.injective B E

  let toV : B →+* ↥V := (algebraMap B E).codRestrict V.toSubring hBV
  let 𝔮 : Ideal B := (maximalIdeal ↥V).comap toV
  haveI h𝔮p : 𝔮.IsPrime := Ideal.comap_isPrime toV _
  have hmem𝔮 : ∀ b : B, b ∈ 𝔮 ↔ algebraMap B E b ∈ V.nonunits := by
    intro b
    rw [Ideal.mem_comap]
    exact (ValuationSubring.coe_mem_nonunits_iff (A := V) (a := toV b)).symm

  have h𝔮 : 𝔮 ≠ ⊥ := by
    intro h0
    apply hV
    rw [eq_top_iff]
    intro e _
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) e
    have hy0 : (y : B) ≠ 0 := nonZeroDivisors.ne_zero hy
    have hyu : algebraMap B E y ∉ V.nonunits := by
      rw [← hmem𝔮, h0, Ideal.mem_bot]; exact hy0
    have hyu' : IsUnit (⟨algebraMap B E y, hBV y⟩ : ↥V) := by
      by_contra hu
      exact hyu ((ValuationSubring.coe_mem_nonunits_iff (A := V) (a := ⟨_, hBV y⟩)).2
        ((mem_maximalIdeal _).2 hu))
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hyu'
    have hwval : (w : E) = (algebraMap B E y)⁻¹ := eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)
    rw [div_eq_mul_inv, ← hwval]
    exact V.mul_mem _ _ (hBV x) w.2

  by_cases hc0 : c = 0
  · refine ⟨0, 1, one_ne_zero, ?_, by rw [hc0, zero_mul, map_zero]⟩
    rw [← hmem𝔮]
    exact fun h => h𝔮p.ne_top ((Ideal.eq_top_iff_one _).2 h)

  have hS : 𝔮.primeCompl ≤ nonZeroDivisors B := Ideal.primeCompl_le_nonZeroDivisors 𝔮
  let W : Subalgebra B E := Localization.subalgebra.ofField E 𝔮.primeCompl hS
  haveI : IsDiscreteValuationRing ↥W :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B h𝔮 ↥W
  have hmemW : ∀ x : E, x ∈ W ↔ ∃ (a s : B) (_ : s ∈ 𝔮.primeCompl),
      x = algebraMap B E a * (algebraMap B E s)⁻¹ := fun x => Iff.rfl
  rcases ValuationRing.isInteger_or_isInteger ↥W c with ⟨w, hw⟩ | ⟨w, hw⟩
  ·
    have hcW : c ∈ W := by rw [← hw]; exact w.2
    obtain ⟨a, s, hs, hc'⟩ := (hmemW c).1 hcW
    have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ 𝔮.zero_mem)
    refine ⟨a, s, hs0, fun h => hs ((hmem𝔮 s).2 h), ?_⟩
    rw [hc', mul_assoc, inv_mul_cancel₀ ((map_ne_zero_iff _ hinj).2 hs0), mul_one]
  ·
    have hcW : c⁻¹ ∈ W := by rw [← hw]; exact w.2
    obtain ⟨a, s, hs, hc'⟩ := (hmemW _).1 hcW
    have hs0 : s ≠ 0 := fun h0 => hs (h0 ▸ 𝔮.zero_mem)
    have hs0' : algebraMap B E s ≠ 0 := (map_ne_zero_iff _ hinj).2 hs0
    have key : c * algebraMap B E a = algebraMap B E s := by
      have h1 : c⁻¹ * algebraMap B E s = algebraMap B E a := by
        rw [hc', mul_assoc, inv_mul_cancel₀ hs0', mul_one]
      calc c * algebraMap B E a = c * (c⁻¹ * algebraMap B E s) := by rw [h1]
        _ = algebraMap B E s := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have ha : a ∉ 𝔮 := by
      intro ha
      apply hs
      change s ∈ 𝔮
      rw [hmem𝔮] at ha ⊢
      rw [ValuationSubring.coe_mem_nonunits_iff (A := V) (a := ⟨_, hBV a⟩)] at ha
      have := (maximalIdeal ↥V).mul_mem_left ⟨c, hc⟩ ha
      have hval : (⟨c, hc⟩ : ↥V) * ⟨algebraMap B E a, hBV a⟩ = ⟨algebraMap B E s, hBV s⟩ := Subtype.ext key
      rw [hval] at this
      exact (ValuationSubring.coe_mem_nonunits_iff (A := V) (a := ⟨_, hBV s⟩)).2 this
    have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ 𝔮.zero_mem)
    exact ⟨s, a, ha0, fun h => ha ((hmem𝔮 a).2 h), key⟩

end GenLoc

open BDescL1 in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {L : Type} [Field L] [CharZero L] (A : ValuationSubring L)
    (C' : Subring L) (hC'A : ∀ c : L, c ∈ C' → c ∈ A) [IsDomain ↥C'] [IsDiscreteValuationRing ↥C'] (ϖ' : ↥C') (hϖ'irr : Irreducible ϖ')
    (hϖ' : ∀ d : ↥C', IsLocalRing.residue ↥A ⟨(d : L), hC'A d d.2⟩ = 0 ↔ ∃ d' : ↥C', d = ϖ' * d')
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C' a)
    (S : Finset L) (hS : ∀ s ∈ S, s ∈ A) :
    ∃ (C'' : Subring L) (_ : IsDomain ↥C'') (_ : IsDiscreteValuationRing ↥C'') (ϖ'' : ↥C'') (e : ℕ) (R : Subring L)
      (hC'C'' : C' ≤ C'') (hC'R : C' ≤ R) (hC''A : ∀ c : L, c ∈ C'' → c ∈ A),
      (∀ s ∈ S, s ∈ C'') ∧

      (∀ c : L, c ∈ C'' ↔ c ∈ A ∧ c ∈ Subfield.closure ((C' : Set L) ∪ ↑S)) ∧

      Irreducible ϖ'' ∧
      (∀ d : ↥C'', IsLocalRing.residue ↥A ⟨(d : L), hC''A d d.2⟩ = 0 ↔ ∃ d' : ↥C'', d = ϖ'' * d') ∧

      1 ≤ e ∧ (∃ v : L, v ∈ C'' ∧ v⁻¹ ∈ C'' ∧ ((ϖ' : ↥C') : L) = v * ((ϖ'' : ↥C'') : L) ^ e) ∧

      R ≤ C'' ∧ (letI : Algebra ↥C' ↥R := (Subring.inclusion hC'R).toAlgebra; Module.Finite ↥C' ↥R) ∧
      (∀ c : L, c ∈ C'' → ∃ r s : L, r ∈ R ∧ s ∈ R ∧ s ≠ 0 ∧ s⁻¹ ∈ C'' ∧ c * s = r) := by
  classical

  have hϖ'0 : ϖ' ≠ 0 := hϖ'irr.ne_zero
  have hϖ'L0 : ((ϖ' : ↥C') : L) ≠ 0 := fun h => hϖ'0 (Subtype.ext h)
  have hϖ'inv : ((ϖ' : ↥C') : L)⁻¹ ∉ A :=
    (residue_eq_zero_iff_inv_not_mem A _ (hC'A _ ϖ'.2) hϖ'L0).mp ((hϖ' ϖ').mpr ⟨1, (mul_one _).symm⟩)
  have hmaxC' : maximalIdeal ↥C' = Ideal.span {ϖ'} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ').mp hϖ'irr
  set K₁ : Subfield L := Subfield.closure (C' : Set L) with hK₁
  have hC'K₁ : ∀ c : L, c ∈ C' → c ∈ K₁ := fun c hc => Subfield.subset_closure hc
  have hK₁frac : ∀ x : L, x ∈ K₁ → ∃ a b : L, a ∈ C' ∧ b ∈ C' ∧ b ≠ 0 ∧ x = a / b := by
    intro x hx
    rw [hK₁, Subfield.mem_closure_iff] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    rw [Subring.closure_eq] at hy hz
    by_cases hz0 : z = 0
    · exact ⟨0, 1, C'.zero_mem, C'.one_mem, one_ne_zero, by rw [hz0, div_zero, zero_div]⟩
    · exact ⟨y, z, hy, hz, hz0, rfl⟩

  have hnu : ∀ c : ↥C', ¬ IsUnit c → (c : L) ≠ 0 → ((c : ↥C') : L)⁻¹ ∉ A := by
    intro c hc hc0
    have hcm : c ∈ maximalIdeal ↥C' := hc
    rw [hmaxC', Ideal.mem_span_singleton'] at hcm
    obtain ⟨d, hd⟩ := hcm
    exact (residue_eq_zero_iff_inv_not_mem A _ (hC'A _ c.2) hc0).mp ((hϖ' c).mpr ⟨d, by rw [← hd, mul_comm]⟩)

  have hAK₁ : ∀ x : L, x ∈ K₁ → x ∈ A → x ∈ C' := by
    intro x hxK hxA
    obtain ⟨a, b, ha, hb, hb0, rfl⟩ := hK₁frac x hxK
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond (⟨a, ha⟩ : ↥C') ⟨b, hb⟩
    · have hcL : a * (c : L) = b := congrArg Subtype.val hc
      by_cases ha0 : a = 0
      · rw [ha0, zero_div]; exact C'.zero_mem
      have hc0 : ((c : ↥C') : L) ≠ 0 := by
        intro h; apply hb0; rw [← hcL, h, mul_zero]
      have hab : a / b = ((c : ↥C') : L)⁻¹ := by
        rw [← hcL, div_mul_eq_div_div, div_self ha0, one_div]
      rw [hab] at hxA ⊢
      by_contra hcon
      exact hnu c (fun hu => hcon (inv_mem_of_isUnit C' c hu)) hc0 hxA
    · have hcL : b * (c : L) = a := congrArg Subtype.val hc
      rw [← hcL, mul_comm, mul_div_assoc, div_self hb0, mul_one]
      exact c.2

  let iCK : ↥C' →+* ↥K₁ :=
    { toFun := fun c => ⟨(c : L), hC'K₁ c c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hiCK : Function.Injective iCK := by
    intro x y h
    have h' := congrArg (fun z : ↥K₁ => (z : L)) h
    exact Subtype.ext h'
  letI algCK : Algebra ↥C' ↥K₁ := iCK.toAlgebra
  haveI : IsScalarTower ↥C' ↥K₁ L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let E : IntermediateField ↥K₁ L := IntermediateField.adjoin ↥K₁ (↑S : Set L)
  have hEclos : ∀ c : L, c ∈ E ↔ c ∈ Subfield.closure ((C' : Set L) ∪ ↑S) := by
    intro c
    have hr : Set.range (algebraMap (↥K₁) L) = (K₁ : Set L) := by
      ext x; constructor
      · rintro ⟨y, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
    have h2 : Subfield.closure ((K₁ : Set L) ∪ ↑S) = Subfield.closure ((C' : Set L) ∪ ↑S) := by
      apply le_antisymm
      · rw [Subfield.closure_le]
        rintro x (hx | hx)
        · exact Subfield.closure_mono Set.subset_union_left (by rw [hK₁] at hx; exact hx)
        · exact Subfield.subset_closure (Or.inr hx)
      · exact Subfield.closure_mono (Set.union_subset_union_left _ (fun x hx => hC'K₁ x hx))
    rw [← IntermediateField.mem_toSubfield, IntermediateField.adjoin_toSubfield, hr, h2]
  have hint : ∀ s ∈ (↑S : Set L), IsIntegral ↥K₁ s := by
    intro s hs
    exact ((halg s (hS s hs)).extendScalars hiCK).isIntegral
  haveI hEfin : FiniteDimensional ↥K₁ ↥E := IntermediateField.finiteDimensional_adjoin hint
  haveI : Algebra.IsSeparable ↥K₁ ↥E := inferInstance

  letI algCE : Algebra ↥C' ↥E := ((algebraMap ↥K₁ ↥E).comp iCK).toAlgebra
  haveI : IsScalarTower ↥C' ↥K₁ ↥E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥C' ↥E L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hfracCK : IsFractionRing ↥C' ↥K₁ := by
    rw [IsFractionRing, isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      have hy0 : ((y : ↥C') : L) ≠ 0 := fun h => nonZeroDivisors.ne_zero hy (Subtype.ext h)
      exact IsUnit.mk0 _ (fun h => hy0 (congrArg (fun z : ↥K₁ => (z : L)) h))
    · intro z
      obtain ⟨a, b, ha, hb, hb0, hz⟩ := hK₁frac (z : L) z.2
      refine ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, mem_nonZeroDivisors_of_ne_zero (fun h => hb0 (congrArg Subtype.val h))⟩), ?_⟩
      apply Subtype.ext
      show (z : L) * b = a
      rw [hz, div_mul_eq_mul_div, mul_div_assoc, div_self hb0, mul_one]
    · intro x y h
      exact ⟨1, by rw [hiCK h]⟩

  let O' : ValuationSubring ↥E := A.comap (algebraMap ↥E L)
  have hmemO' : ∀ x : ↥E, x ∈ O' ↔ (x : L) ∈ A := fun x => Iff.rfl
  have hO'ne : O' ≠ ⊤ := by
    intro h
    apply hϖ'inv
    have : (algebraMap ↥C' ↥E ϖ')⁻¹ ∈ O' := by rw [h]; exact ValuationSubring.mem_top _
    exact this
  haveI : Ring.KrullDimLE 1 ↥C' := inferInstance
  have hO'dvr : IsDiscreteValuationRing ↥O' :=
    ValuationSubring.isDiscreteValuationRing_of_algebraMap_mem_of_finite (A := ↥C') (K := ↥K₁) (L := ↥E) O'
      (fun c => (hmemO' _).mpr (hC'A c c.2)) hO'ne

  have hEinj : Function.Injective (algebraMap ↥E L) := Subtype.coe_injective
  let C'' : Subring L := O'.toSubring.map (algebraMap ↥E L)
  have hmemC'' : ∀ c : L, c ∈ C'' ↔ c ∈ A ∧ c ∈ E := by
    intro c
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
    · rintro ⟨hcA, hcE⟩; exact ⟨⟨c, hcE⟩, hcA, rfl⟩
  let eC : ↥O'.toSubring ≃+* ↥C'' := O'.toSubring.equivMapOfInjective (algebraMap ↥E L) hEinj
  haveI hC''dvr : IsDiscreteValuationRing ↥C'' := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (A := ↥O') eC
  have hC''A : ∀ c : L, c ∈ C'' → c ∈ A := fun c hc => ((hmemC'' c).mp hc).1
  have hC''E : ∀ c : L, c ∈ C'' → c ∈ E := fun c hc => ((hmemC'' c).mp hc).2
  have hC'C'' : C' ≤ C'' := fun c hc =>
    (hmemC'' c).mpr ⟨hC'A c hc, (hEclos c).mpr (Subfield.subset_closure (Or.inl hc))⟩
  have hSC'' : ∀ s ∈ S, s ∈ C'' := fun s hs =>
    (hmemC'' s).mpr ⟨hS s hs, (hEclos s).mpr (Subfield.subset_closure (Or.inr hs))⟩

  have hunitC'' : ∀ d : ↥C'', (d : L) ≠ 0 → (IsUnit d ↔ ((d : L))⁻¹ ∈ A) := by
    intro d hd0
    constructor
    · intro hu; exact hC''A _ (inv_mem_of_isUnit C'' d hu)
    · intro hi
      have : ((d : L))⁻¹ ∈ C'' := (hmemC'' _).mpr ⟨hi, inv_mem (hC''E _ d.2)⟩
      have := isUnit_of_inv_mem C'' (d : L) d.2 this hd0
      exact this
  have hresC'' : ∀ d : ↥C'', IsLocalRing.residue ↥A ⟨(d : L), hC''A d d.2⟩ = 0 ↔ d ∈ maximalIdeal ↥C'' := by
    intro d
    by_cases hd0 : (d : L) = 0
    · have hd : d = 0 := Subtype.ext hd0
      have : (⟨(d : L), hC''A d d.2⟩ : ↥A) = 0 := Subtype.ext hd0
      rw [this, map_zero, hd]
      exact ⟨fun _ => Ideal.zero_mem _, fun _ => rfl⟩
    · rw [residue_eq_zero_iff_inv_not_mem A _ _ hd0, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunitC'' d hd0]

  obtain ⟨ϖ'', hϖ''⟩ := IsDiscreteValuationRing.exists_irreducible ↥C''
  have hmaxC'' : maximalIdeal ↥C'' = Ideal.span {ϖ''} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ'').mp hϖ''
  have hdiv : ∀ d : ↥C'', IsLocalRing.residue ↥A ⟨(d : L), hC''A d d.2⟩ = 0 ↔ ∃ d' : ↥C'', d = ϖ'' * d' := by
    intro d
    rw [hresC'', hmaxC'', Ideal.mem_span_singleton']
    constructor
    · rintro ⟨a, ha⟩; exact ⟨a, by rw [← ha, mul_comm]⟩
    · rintro ⟨a, ha⟩; exact ⟨a, by rw [ha, mul_comm]⟩
  let p' : ↥C'' := ⟨((ϖ' : ↥C') : L), hC'C'' (ϖ'.2)⟩
  have hp'0 : p' ≠ 0 := fun h => hϖ'L0 (congrArg Subtype.val h)
  have hp'm : p' ∈ maximalIdeal ↥C'' := by
    rw [← hresC'']
    exact (residue_eq_zero_iff_inv_not_mem A _ _ hϖ'L0).mpr hϖ'inv
  obtain ⟨e, u, hue⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp'0 hϖ''
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hue
      have : IsUnit p' := hue ▸ u.isUnit
      exact (IsLocalRing.mem_maximalIdeal _).mp hp'm this
    · exact h
  have hv : ∃ v : L, v ∈ C'' ∧ v⁻¹ ∈ C'' ∧ ((ϖ' : ↥C') : L) = v * ((ϖ'' : ↥C'') : L) ^ e := by
    refine ⟨((u : ↥C'') : L), (u : ↥C'').2, inv_mem_of_isUnit C'' _ u.isUnit, ?_⟩
    have := congrArg Subtype.val hue
    simpa only [Subring.coe_mul, Subring.coe_pow] using this

  haveI : IsIntegrallyClosed ↥C' := inferInstance
  let B : Subalgebra ↥C' ↥E := integralClosure ↥C' ↥E
  haveI hBfin : Module.Finite ↥C' ↥B := IsIntegralClosure.finite ↥C' ↥K₁ ↥E ↥B
  haveI hBfrac : IsFractionRing ↥B ↥E := IsIntegralClosure.isFractionRing_of_finite_extension ↥C' ↥K₁ ↥E ↥B
  haveI hBded : IsDedekindDomain ↥B := IsIntegralClosure.isDedekindDomain ↥C' ↥K₁ ↥E ↥B
  let R : Subring L := B.toSubring.map (algebraMap ↥E L)
  have hC'R : C' ≤ R := fun c hc =>
    ⟨algebraMap ↥C' ↥E ⟨c, hc⟩, (mem_integralClosure_iff _ _).mpr isIntegral_algebraMap, rfl⟩

  let iCA : ↥C' →+* ↥A :=
    { toFun := fun c => ⟨(c : L), hC'A c c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI algCA : Algebra ↥C' ↥A := iCA.toAlgebra
  haveI : IsScalarTower ↥C' ↥A L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hBA : ∀ x : ↥E, x ∈ B → (x : L) ∈ A := by
    intro x hx
    have h1 : IsIntegral ↥C' (algebraMap ↥E L x) := ((mem_integralClosure_iff _ _).mp hx).algebraMap
    exact mem_of_isIntegral A h1.tower_top
  have hRC'' : R ≤ C'' := by
    rintro r ⟨x, hx, rfl⟩
    exact (hmemC'' _).mpr ⟨hBA x hx, x.2⟩
  have hRfin : (letI : Algebra ↥C' ↥R := (Subring.inclusion hC'R).toAlgebra; Module.Finite ↥C' ↥R) := by
    letI algCR : Algebra ↥C' ↥R := (Subring.inclusion hC'R).toAlgebra
    let g : ↥B →ₐ[↥C'] ↥R :=
      { toFun := fun x => ⟨((x : ↥E) : L), ⟨(x : ↥E), x.2, rfl⟩⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun x y => Subtype.ext rfl
        map_zero' := Subtype.ext rfl
        map_add' := fun x y => Subtype.ext rfl
        commutes' := fun c => Subtype.ext rfl }
    have hsurj : Function.Surjective g := by
      rintro ⟨r, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    exact Module.Finite.of_surjective g.toLinearMap hsurj

  have hBO' : ∀ b : ↥B, algebraMap ↥B ↥E b ∈ O' := fun b => (hmemO' _).mpr (hBA b b.2)
  have hloc : ∀ c : L, c ∈ C'' → ∃ r s : L, r ∈ R ∧ s ∈ R ∧ s ≠ 0 ∧ s⁻¹ ∈ C'' ∧ c * s = r := by
    intro c hc
    obtain ⟨b, s, hs0, hsu, hcs⟩ := GenLoc.exists_frac_unit_of_mem_valuationSubring O' hBO' hO'ne
      ⟨c, hC''E c hc⟩ ((hmemO' _).mpr (hC''A c hc))
    have hs0E : algebraMap ↥B ↥E s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective ↥B ↥E)).mpr hs0
    have hsunit : IsUnit (⟨algebraMap ↥B ↥E s, hBO' s⟩ : ↥O') := by
      by_contra hu
      exact hsu ((ValuationSubring.coe_mem_nonunits_iff (A := O') (a := ⟨_, hBO' s⟩)).2
        ((IsLocalRing.mem_maximalIdeal _).2 hu))
    have hsi : (algebraMap ↥B ↥E s)⁻¹ ∈ O' := inv_mem_of_isUnit O'.toSubring ⟨algebraMap ↥B ↥E s, hBO' s⟩ hsunit
    refine ⟨((b : ↥E) : L), ((s : ↥E) : L), ⟨(b : ↥E), b.2, rfl⟩, ⟨(s : ↥E), s.2, rfl⟩,
      fun h => hs0E (Subtype.ext h), (hmemC'' _).mpr ⟨hsi, inv_mem (s : ↥E).2⟩, ?_⟩
    exact congrArg Subtype.val hcs

  exact ⟨C'', inferInstance, hC''dvr, ϖ'', e, R, hC'C'', hC'R, hC''A, hSC'',
    fun c => (hmemC'' c).trans ⟨fun h => ⟨h.1, (hEclos c).mp h.2⟩, fun h => ⟨h.1, (hEclos c).mpr h.2⟩⟩,
    hϖ'', hdiv, he1, hv, hRC'', hRfin, hloc⟩

end S_ValuationSubring_exists_layer_isDiscreteValuationRing_of_finite_of_isAlgebraic_of_irreducible
end P2MW
export P2MW.S_ValuationSubring_exists_layer_isDiscreteValuationRing_of_finite_of_isAlgebraic_of_irreducible (solution)
