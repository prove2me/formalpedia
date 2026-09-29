-- Prove2me | solution 1 for ValuationSubring.exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/39a83941-a477-55e8-a5de-e53d87720049

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq

set_option autoImplicit false

open scoped Pointwise
open Polynomial

noncomputable section

namespace ResidueSurjAux

theorem exists_residue_apply_eq {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    {σ : L ≃ₐ[ℚ] L} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (a : ↥A) :
    ∃ h : σ (a : L) ∈ A, IsLocalRing.residue ↥A ⟨σ (a : L), h⟩ = IsLocalRing.residue ↥A a := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hσ
  have hval : ((d • a : ↥A) : L) = ((A.decompositionSubgroup ℚ).subtype d) (a : L) := rfl
  refine ⟨hval ▸ (d • a).2, ?_⟩
  have h1 : (⟨((A.decompositionSubgroup ℚ).subtype d) (a : L), hval ▸ (d • a).2⟩ : ↥A) = d • a := Subtype.ext hval.symm
  rw [h1, IsLocalRing.ResidueField.residue_smul]
  have h2 := RingEquiv.congr_fun (MonoidHom.mem_ker.mp hd) (IsLocalRing.residue ↥A a)
  simpa using h2

theorem isUnit_intCast {L : Type*} [Field L] [CharZero L] (A : ValuationSubring L) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) (m : ℤ) (hm : ¬ (q : ℤ) ∣ m) : IsUnit ((m : ↥A)) := by
  rw [ValuationSubring.LiesOverPrime] at hA
  have hqℤ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  obtain ⟨s, t, hst⟩ := (Prime.coprime_iff_not_dvd hqℤ).mpr hm

  by_contra hmu
  have hmn : ((m : ↥A) : L) ∈ A.nonunits := (ValuationSubring.coe_mem_nonunits_iff).mpr
    ((IsLocalRing.mem_maximalIdeal _).mpr hmu)
  have h1 : ((1 : ↥A) : L) ∈ A.nonunits := by
    have : (1 : ↥A) = (s : ↥A) * (q : ↥A) + (t : ↥A) * (m : ↥A) := by
      apply Subtype.ext
      push_cast
      exact_mod_cast hst.symm
    rw [this]
    push_cast
    rw [ValuationSubring.mem_nonunits_iff] at hA hmn ⊢
    refine lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      calc A.valuation (s : L) * A.valuation (q : L) ≤ 1 * A.valuation (q : L) :=
            mul_le_mul_left ((A.valuation_le_one_iff _).mpr (intCast_mem A s)) _
        _ < 1 := by rw [one_mul]; exact hA
    · rw [map_mul]
      calc A.valuation (t : L) * A.valuation (m : L) ≤ 1 * A.valuation (m : L) :=
            mul_le_mul_left ((A.valuation_le_one_iff _).mpr (intCast_mem A t)) _
        _ < 1 := by rw [one_mul]; exact hmn
  rw [ValuationSubring.mem_nonunits_iff, OneMemClass.coe_one, map_one] at h1
  exact lt_irrefl _ h1

theorem charP_residueField {L : Type*} [Field L] [CharZero L] (A : ValuationSubring L) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) : CharP (IsLocalRing.ResidueField ↥A) q := by
  refine (CharP.charP_iff_prime_eq_zero hq).mpr ?_
  have hmem : ((q : ↥A)) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; exact_mod_cast hA
  have : IsLocalRing.residue ↥A (q : ↥A) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  simpa using this

theorem exists_int_poly_map_ne_zero {L : Type*} [Field L] [CharZero L] [Algebra ℚ L] (A : ValuationSubring L)
    {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) (a : ↥A) (ha : IsAlgebraic ℚ (a : L)) :
    ∃ f : ℤ[X], f.map (Int.castRingHom (ZMod q)) ≠ 0 ∧ eval₂ (Int.castRingHom ↥A) a f = 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨p, hp0, hp⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr ha
  refine ⟨p.primPart, ?_, ?_⟩
  · intro h0
    have hdvd : C (q : ℤ) ∣ p.primPart := by
      rw [C_dvd_iff_dvd_coeff]
      intro n
      have := congrArg (fun f => f.coeff n) h0
      simp only [coeff_map, coeff_zero, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact this
    have := p.isPrimitive_primPart (q : ℤ) hdvd
    exact (Nat.prime_iff_prime_int.mp hq).not_unit this
  · have h1 : aeval (a : L) p = aeval (a : L) (C p.content) * aeval (a : L) p.primPart := by
      rw [← map_mul, ← p.eq_C_content_mul_primPart]
    rw [hp, aeval_C, eq_comm, mul_eq_zero] at h1
    have hc : algebraMap ℤ L p.content ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (algebraMap ℤ L).injective_int, content_eq_zero_iff]
      exact hp0
    have h2 : aeval (a : L) p.primPart = 0 := h1.resolve_left hc
    apply Subtype.val_injective
    change A.subtype (eval₂ (Int.castRingHom ↥A) a p.primPart) = ((0 : ↥A) : L)
    rw [Polynomial.hom_eval₂, show A.subtype.comp (Int.castRingHom ↥A) = algebraMap ℤ L from RingHom.ext_int _ _,
      ← aeval_def, ZeroMemClass.coe_zero]
    exact h2

end ResidueSurjAux

end

open ResidueSurjAux in

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime] (hA : A.LiesOverPrime q)
    (x : IsLocalRing.ResidueField ↥A) :
    ∃ y : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))),
      (IsLocalRing.residue ↥A)
          ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
              (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), y.2⟩ = x := by
  classical
  haveI hchar : CharP (IsLocalRing.ResidueField ↥A) q := charP_residueField A (Fact.out) hA
  have hq : q.Prime := Fact.out

  let red' : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))) → (IsLocalRing.ResidueField ↥A) :=
    fun y => IsLocalRing.residue ↥A ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), y.2⟩
  have red'_mul : ∀ y y', red' (y * y') = red' y * red' y' := fun y y' => by
    simp only [red']; rw [← map_mul]; rfl
  have red'_add : ∀ y y', red' (y + y') = red' y + red' y' := fun y y' => by
    simp only [red']; rw [← map_add]; rfl
  have red'_one : red' 1 = 1 := by simp only [red']; rw [← (IsLocalRing.residue ↥A).map_one]; rfl
  have red'_zero : red' 0 = 0 := by simp only [red']; rw [← (IsLocalRing.residue ↥A).map_zero]; rfl
  have red'_neg : ∀ y, red' (-y) = -red' y := fun y => by simp only [red']; rw [← map_neg]; rfl
  suffices hsurj : ∃ y, red' y = x by obtain ⟨y, hy⟩ := hsurj; exact ⟨y, hy⟩

  let k' : Subfield (IsLocalRing.ResidueField ↥A) :=
    { carrier := Set.range red'
      mul_mem' := by rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩; exact ⟨y * y', red'_mul y y'⟩
      one_mem' := ⟨1, red'_one⟩
      add_mem' := by rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩; exact ⟨y + y', red'_add y y'⟩
      zero_mem' := ⟨0, red'_zero⟩
      neg_mem' := by rintro _ ⟨y, rfl⟩; exact ⟨-y, red'_neg y⟩
      inv_mem' := by
        rintro _ ⟨y, rfl⟩
        by_cases h0 : red' y = 0
        · exact ⟨y, by rw [h0, inv_zero]⟩
        · have hyu : IsUnit (⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), y.2⟩ : ↥A) := by
            by_contra hnu
            exact h0 ((IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hnu))
          have hy0 : (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))) ≠ 0 := by
            intro h; apply h0
            show IsLocalRing.residue ↥A ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), y.2⟩ = 0
            have : (⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), y.2⟩ : ↥A) = 0 := Subtype.ext (by simp [h])
            rw [this, map_zero]
          obtain ⟨u, hu⟩ := hyu
          have hval : ((u : ↥A) : (AlgebraicClosure ℚ)) = algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))) := congrArg Subtype.val hu
          have hmul : (((u⁻¹ : (↥A)ˣ) : ↥A) : (AlgebraicClosure ℚ)) * algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))) = 1 := by
            rw [← hval, ← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one]
          have hinvA : algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)))⁻¹) ∈ A := by
            rw [map_inv₀, inv_eq_of_mul_eq_one_left hmul]
            exact Subtype.coe_prop _
          refine ⟨⟨(y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)))⁻¹, hinvA⟩, ?_⟩
          apply eq_inv_of_mul_eq_one_right
          rw [← red'_mul]
          have : y * ⟨(y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)))⁻¹, hinvA⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hy0)
          rw [this, red'_one] }
  have hk'mem : ∀ y, red' y ∈ k' := fun y => ⟨y, rfl⟩

  haveI : CharP ↥k' q := by
    refine (CharP.charP_iff_prime_eq_zero hq).mpr (k'.subtype.injective ?_)
    rw [map_natCast, map_zero, CharP.cast_eq_zero]
  letI : Algebra (ZMod q) ↥k' := ZMod.algebra _ q
  have halgL : ∀ b : (AlgebraicClosure ℚ), IsAlgebraic ℚ b := fun b => by
    convert (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic b
    rfl
    rfl
  haveI : Algebra.IsAlgebraic (ZMod q) ↥k' := by
    refine ⟨fun z => ?_⟩
    obtain ⟨y, hy⟩ := z.2
    have halg : IsAlgebraic ℚ (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) (y : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)))) := halgL _
    obtain ⟨f, hf0, hf⟩ := exists_int_poly_map_ne_zero A hq hA ⟨_, y.2⟩ halg
    refine ⟨f.map (Int.castRingHom (ZMod q)), hf0, ?_⟩
    apply k'.subtype.injective
    rw [map_zero, aeval_def, Polynomial.hom_eval₂, eval₂_map,
      show (k'.subtype.comp (algebraMap (ZMod q) ↥k')).comp (Int.castRingHom (ZMod q)) =
        (IsLocalRing.residue ↥A).comp (Int.castRingHom ↥A) from RingHom.ext_int _ _]
    have hz : k'.subtype z = IsLocalRing.residue ↥A ⟨_, y.2⟩ := hy.symm
    rw [hz, ← Polynomial.hom_eval₂, hf, map_zero]
  haveI : PerfectField ↥k' := Algebra.IsAlgebraic.perfectField (K := ZMod q)

  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  have haint : IsIntegral ℚ (a : (AlgebraicClosure ℚ)) := (halgL _).isIntegral
  have hfinL : {b : (AlgebraicClosure ℚ) | ∃ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : (AlgebraicClosure ℚ)) = b}.Finite := by
    refine ((minpoly ℚ (a : (AlgebraicClosure ℚ))).rootSet_finite (AlgebraicClosure ℚ)).subset ?_
    rintro _ ⟨σ, -, rfl⟩
    rw [mem_rootSet]
    exact ⟨minpoly.ne_zero haint, by rw [aeval_algHom_apply, minpoly.aeval, map_zero]⟩
  have hfin : (Subtype.val ⁻¹' {b : (AlgebraicClosure ℚ) | ∃ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : (AlgebraicClosure ℚ)) = b} : Set ↥A).Finite :=
    hfinL.preimage Subtype.val_injective.injOn
  set F := hfin.toFinset with hF
  have hmemF : ∀ b : ↥A, b ∈ F ↔ ∃ σ ∈ A.inertiaSubgroupIn ℚ, σ (a : (AlgebraicClosure ℚ)) = (b : (AlgebraicClosure ℚ)) := fun b => by
    rw [hF, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]
  have haF : a ∈ F := (hmemF a).mpr ⟨1, one_mem _, rfl⟩

  have hres : ∀ b ∈ F, IsLocalRing.residue ↥A b = IsLocalRing.residue ↥A a := by
    intro b hb
    obtain ⟨σ, hσ, hb⟩ := (hmemF b).mp hb
    obtain ⟨h, hres⟩ := exists_residue_apply_eq A hσ a
    rw [← hres]; congr 1; exact Subtype.ext hb.symm

  set PA : (↥A)[X] := ∏ b ∈ F, (X - C b) with hPA
  have hPAmonic : PA.Monic := monic_prod_of_monic _ _ fun b _ => monic_X_sub_C b
  have hPAres : PA.map (IsLocalRing.residue ↥A) = (X - C (IsLocalRing.residue ↥A a)) ^ F.card := by
    rw [hPA, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    rw [Finset.prod_congr rfl (fun b hb => by rw [hres b hb]), Finset.prod_const]

  have hstab : ∀ {τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)} (hτ : τ ∈ A.inertiaSubgroupIn ℚ) (b : ↥A), τ (b : (AlgebraicClosure ℚ)) ∈ A :=
    fun hτ b => (exists_residue_apply_eq A hτ b).1
  have hcoeffKI : ∀ k, ((PA.coeff k : ↥A) : (AlgebraicClosure ℚ)) ∈ (IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) := by
    intro k
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have hτ' : τ⁻¹ ∈ A.inertiaSubgroupIn ℚ := inv_mem hτ

    have hP : (PA.map A.subtype).map (τ : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ)) = PA.map A.subtype := by
      rw [hPA, Polynomial.map_prod, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, RingHom.coe_coe]
      refine Finset.prod_nbij' (fun b => (⟨τ (b : (AlgebraicClosure ℚ)), hstab hτ b⟩ : ↥A)) (fun b => (⟨τ⁻¹ (b : (AlgebraicClosure ℚ)), hstab hτ' b⟩ : ↥A))
        ?_ ?_ ?_ ?_ ?_
      · intro b hb
        obtain ⟨σ, hσ, hb⟩ := (hmemF b).mp hb
        exact (hmemF _).mpr ⟨τ * σ, mul_mem hτ hσ, by rw [AlgEquiv.mul_apply, hb]⟩
      · intro b hb
        obtain ⟨σ, hσ, hb⟩ := (hmemF b).mp hb
        exact (hmemF _).mpr ⟨τ⁻¹ * σ, mul_mem hτ' hσ, by rw [AlgEquiv.mul_apply, hb]⟩
      · intro b _; apply Subtype.ext; simp
      · intro b _; apply Subtype.ext; simp
      · intro b _; rfl
    have := congrArg (fun f => f.coeff k) hP
    simp only [coeff_map, RingHom.coe_coe] at this
    exact this

  set n := F.card with hn
  have hn0 : n ≠ 0 := Finset.card_ne_zero_of_mem haF
  have hlifts : (X - C (IsLocalRing.residue ↥A a)) ^ n ∈ Polynomial.lifts (algebraMap ↥k' (IsLocalRing.ResidueField ↥A)) := by
    rw [lifts_iff_coeff_lifts]
    intro k
    refine ⟨⟨red' ⟨⟨_, hcoeffKI k⟩, (PA.coeff k).2⟩, hk'mem _⟩, ?_⟩
    rw [← hPAres, coeff_map]
    rfl
  obtain ⟨Q, hQmap, -, hQmonic⟩ := lifts_and_natDegree_eq_and_monic hlifts ((monic_X_sub_C _).pow n)

  set x := IsLocalRing.residue ↥A a with hx
  have hxint : IsIntegral ↥k' x := by
    refine ⟨Q, hQmonic, ?_⟩
    rw [eval₂_eq_eval_map, hQmap, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow hn0]
  have hsep : (minpoly ↥k' x).Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hxint)
  have hdvd : (minpoly ↥k' x).map (algebraMap ↥k' (IsLocalRing.ResidueField ↥A)) ∣ (X - C x) ^ n := by
    rw [← hQmap]
    refine Polynomial.map_dvd _ (minpoly.dvd _ _ ?_)
    rw [aeval_def, eval₂_eq_eval_map, hQmap, eval_pow, eval_sub, eval_X, eval_C, sub_self, zero_pow hn0]
  have hpow0 : (X - C x) ^ n ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero x)
  have hsplit : ((minpoly ↥k' x).map (algebraMap ↥k' (IsLocalRing.ResidueField ↥A))).Splits :=
    ((Splits.X_sub_C x).pow n).of_dvd hpow0 hdvd
  have hroots : ((minpoly ↥k' x).map (algebraMap ↥k' (IsLocalRing.ResidueField ↥A))).roots = {x} := by
    have hle : ((minpoly ↥k' x).map (algebraMap ↥k' (IsLocalRing.ResidueField ↥A))).roots ≤ n • ({x} : Multiset (IsLocalRing.ResidueField ↥A)) := by
      have := roots.le_of_dvd hpow0 hdvd
      rwa [roots_pow, roots_X_sub_C] at this
    have hall : ∀ b ∈ ((minpoly ↥k' x).map (algebraMap ↥k' (IsLocalRing.ResidueField ↥A))).roots, b = x := fun b hb => by
      have := Multiset.mem_of_le hle hb
      rw [Multiset.mem_nsmul] at this
      exact Multiset.mem_singleton.mp this.2
    have hnodup : ((minpoly ↥k' x).map (algebraMap ↥k' (IsLocalRing.ResidueField ↥A))).roots.Nodup := nodup_roots hsep.map
    have hxmem : x ∈ ((minpoly ↥k' x).map (algebraMap ↥k' (IsLocalRing.ResidueField ↥A))).roots := by
      rw [mem_roots (Polynomial.map_ne_zero (minpoly.ne_zero hxint)), IsRoot.def, eval_map, ← aeval_def]
      exact minpoly.aeval _ _
    have hrep := Multiset.eq_replicate_of_mem hall
    have hle1 : Multiset.card ((minpoly ↥k' x).map (algebraMap ↥k' (IsLocalRing.ResidueField ↥A))).roots ≤ 1 := by
      have := Multiset.nodup_iff_count_le_one.mp hnodup x
      rwa [hrep, Multiset.count_replicate_self] at this
    have hge1 : 1 ≤ Multiset.card ((minpoly ↥k' x).map (algebraMap ↥k' (IsLocalRing.ResidueField ↥A))).roots :=
      Multiset.card_pos.mpr (fun h0 => by rw [h0] at hxmem; exact Multiset.notMem_zero _ hxmem)
    rw [hrep, le_antisymm hle1 hge1]
    rfl
  have hdeg : (minpoly ↥k' x).natDegree = 1 := by
    rw [← Polynomial.natDegree_map (algebraMap ↥k' (IsLocalRing.ResidueField ↥A)), hsplit.natDegree_eq_card_roots, hroots]
    rfl
  obtain ⟨z, hz⟩ := minpoly.natDegree_eq_one_iff.mp hdeg
  obtain ⟨y, hy⟩ := z.2
  exact ⟨y, hy.trans hz⟩

end S_ValuationSubring_exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq
end P2MW
export P2MW.S_ValuationSubring_exists_residue_algebraMap_fixedField_inertiaSubgroupIn_eq (solution)
