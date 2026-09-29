-- Prove2me | solution 1 for WeierstrassCurve.galoisRepUnramifiedAt_of_goodReduction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/ab600ac5-e47f-54d3-9ae3-ba6b10c2dd69

import Theorems.Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_hasGoodReduction
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_galoisRepUnramifiedAt_of_goodReduction
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

noncomputable section

open WeierstrassCurve IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

namespace GoodReductionBridge

variable (q : ℕ) [hq : Fact q.Prime]

scoped instance spanNatPrime_isPrime : (Ideal.span {(q : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hq.out.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hq.out)

abbrev Zq : Type := Localization.AtPrime (Ideal.span {(q : ℤ)})

theorem primeCompl_isUnit (y : (Ideal.span {(q : ℤ)}).primeCompl) :
    IsUnit (algebraMap ℤ ℚ y) := by
  have hy : (y : ℤ) ≠ 0 := fun h => y.2 (h ▸ (Ideal.span {(q : ℤ)}).zero_mem)
  simpa using IsUnit.mk0 ((y : ℤ) : ℚ) (by exact_mod_cast hy)

scoped instance : Algebra (Zq q) ℚ :=
  (IsLocalization.lift (M := (Ideal.span {(q : ℤ)}).primeCompl)
    (g := algebraMap ℤ ℚ) (primeCompl_isUnit q)).toAlgebra

theorem algebraMap_Zq_apply (z : ℤ) : algebraMap (Zq q) ℚ (algebraMap ℤ (Zq q) z) = algebraMap ℤ ℚ z :=
  IsLocalization.lift_eq (M := (Ideal.span {(q : ℤ)}).primeCompl) (g := algebraMap ℤ ℚ)
    (primeCompl_isUnit q) z

scoped instance : IsDiscreteValuationRing (Zq q) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
    (fun h => by
      have h0 : (q : ℤ) = 0 := Ideal.span_singleton_eq_bot.mp h
      exact hq.out.ne_zero (by exact_mod_cast h0)) _

scoped instance : IsFractionRing (Zq q) ℚ := by
  haveI := IsScalarTower.of_algebraMap_eq (R := ℤ) (S := Zq q) (A := ℚ) fun x =>
    (algebraMap_Zq_apply q x).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Ideal.span {(q : ℤ)}).primeCompl (Zq q) ℚ

theorem irreducible_q : Irreducible ((q : ℕ) : Zq q) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := Ideal.span {(q : ℤ)})]
  rw [Ideal.map_span, Set.image_singleton]
  norm_num

theorem isUnit_intCast_of_not_dvd {x : ℤ} (hx : ¬ (q : ℤ) ∣ x) : IsUnit ((x : ℤ) : Zq q) := by
  have hqp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq.out
  have hcop : IsCoprime (q : ℤ) x := hqp.coprime_iff_not_dvd.mpr hx
  obtain ⟨u, v, huv⟩ := hcop.map (algebraMap ℤ (Zq q))
  have h1 : IsUnit (u * algebraMap ℤ (Zq q) (q : ℤ) + v * algebraMap ℤ (Zq q) x) := by
    rw [huv]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
  · exact absurd (by simpa using isUnit_of_mul_isUnit_right h) (irreducible_q q).not_isUnit
  · simpa using isUnit_of_mul_isUnit_right h

theorem hasGoodReduction_map (W : WeierstrassCurve ℤ) (hgood : ¬ (q : ℤ) ∣ W.Δ) :
    (W.map (Int.castRingHom ℚ)).HasGoodReduction (Zq q) := by
  set E := W.map (Int.castRingHom ℚ) with hE
  have hcoef : ∀ z : ℤ, algebraMap (Zq q) ℚ ((z : ℤ) : Zq q) = (z : ℚ) := by
    intro z
    rw [← eq_intCast (algebraMap ℤ (Zq q)) z, algebraMap_Zq_apply, eq_intCast]
  have hInt : IsIntegral (Zq q) E := by
    refine isIntegral_of_exists_lift (Zq q) ⟨W.a₁, ?_⟩ ⟨W.a₂, ?_⟩ ⟨W.a₃, ?_⟩ ⟨W.a₄, ?_⟩ ⟨W.a₆, ?_⟩
    all_goals simp only [hE, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, eq_intCast, hcoef]

  have hval_unit : ∀ r : Zq q, IsUnit r →
      (IsDiscreteValuationRing.maximalIdeal (Zq q)).valuation ℚ (algebraMap (Zq q) ℚ r) = 1 := by
    intro r hr
    rcases lt_or_eq_of_le
        ((IsDiscreteValuationRing.maximalIdeal (Zq q)).valuation_le_one (K := ℚ) r) with h | h
    · exact absurd ((IsDiscreteValuationRing.maximalIdeal (Zq q)).valuation_lt_one_iff_mem
        (K := ℚ) r |>.mp h) (fun hm => (mem_nonunits_iff.mp
          ((IsLocalRing.mem_maximalIdeal r).mp hm)) hr)
    · exact h
  have hΔ : (IsDiscreteValuationRing.maximalIdeal (Zq q)).valuation ℚ E.Δ = 1 := by
    have h1 : E.Δ = algebraMap (Zq q) ℚ ((W.Δ : ℤ) : Zq q) := by
      rw [hcoef, hE, map_Δ, eq_intCast]
    rw [h1]
    exact hval_unit _ (isUnit_intCast_of_not_dvd q hgood)
  haveI := hInt
  have hMin : IsMinimal (Zq q) E := by
    refine ⟨⟨by simpa using hInt, ?_⟩⟩
    intro C hC _
    have hle := (valuation_Δ_aux (Zq q) (C • E)).2
    have heq : ((valuation_Δ_aux (Zq q) ((1 : VariableChange ℚ) • E)) :
        WithZero (Multiplicative ℤ)) = 1 := by
      rw [one_smul, valuation_Δ_aux_eq_of_isIntegral (Zq q) E]
      exact hΔ
    exact Subtype.coe_le_coe.mp (by rw [heq]; exact hle)
  exact { toIsMinimal := hMin, goodReduction := hΔ }

end GoodReductionBridge
p2m_reactivate "P2MW.S_WeierstrassCurve_galoisRepUnramifiedAt_of_goodReduction.GoodReductionBridge"

open GoodReductionBridge in

theorem solution (W : WeierstrassCurve ℤ)
    {q ℓ : ℕ} (hq : q.Prime) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hgood : W.IsGoodPrimeFor q) :
    WeierstrassCurve.Affine.Point.GaloisRepUnramifiedAt (K := AlgebraicClosure ℚ) ℚ
      (W.map (Int.castRingHom ℚ)) ℓ q := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI := hasGoodReduction_map q W hgood
  have hqℓ : ¬ q ∣ ℓ := fun h =>
    hℓq ((Nat.prime_dvd_prime_iff_eq hq hℓ).mp h).symm
  exact WeierstrassCurve.galoisRepUnramifiedAt_of_hasGoodReduction (Zq q)
    (W.map (Int.castRingHom ℚ)) hq (irreducible_q q) hqℓ

end
p2m_reactivate "P2MW.S_WeierstrassCurve_galoisRepUnramifiedAt_of_goodReduction.GoodReductionBridge"

end S_WeierstrassCurve_galoisRepUnramifiedAt_of_goodReduction
end P2MW
export P2MW.S_WeierstrassCurve_galoisRepUnramifiedAt_of_goodReduction (solution)
