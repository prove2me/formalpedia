-- Prove2me | solution 1 for WeierstrassCurve.card_dvd_card_reduction_of_nsmul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/1435eb82-8585-54eb-8ed0-aa3373a0cd04

import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Definitions.Def_EllipticCurve_PointReduction
import Theorems.Thm_WeierstrassCurve_reducePoint_add
import Theorems.Thm_WeierstrassCurve_eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_card_dvd_card_reduction_of_nsmul_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

namespace M4cP1Torsion

open WeierstrassCurve WeierstrassCurve.Affine
open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

section Instantiation

variable (q : ℕ) [hq : Fact q.Prime]

scoped instance spanNatPrime_isPrime : (Ideal.span {(q : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hq.out.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hq.out)

abbrev Zq : Type := Localization.AtPrime (Ideal.span {(q : ℤ)})

noncomputable scoped instance : Algebra (Zq q) ℚ :=
  (IsLocalization.lift (M := (Ideal.span {(q : ℤ)}).primeCompl)
    (g := algebraMap ℤ ℚ) fun y => by
      have hy : (y : ℤ) ≠ 0 := fun h => y.2 (h ▸ (Ideal.span {(q : ℤ)}).zero_mem)
      simpa using IsUnit.mk0 ((y : ℤ) : ℚ) (by exact_mod_cast hy)).toAlgebra

scoped instance : IsDiscreteValuationRing (Zq q) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ
    (fun h => by
      have h0 : (q : ℤ) = 0 := Ideal.span_singleton_eq_bot.mp h
      exact hq.out.ne_zero (by exact_mod_cast h0)) _

theorem algebraMap_Zq_int (x : ℤ) :
    algebraMap (Zq q) ℚ (algebraMap ℤ (Zq q) x) = (x : ℚ) := by
  conv_lhs => rw [RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq]
  simp

scoped instance : IsFractionRing (Zq q) ℚ := by
  haveI := IsScalarTower.of_algebraMap_eq (R := ℤ) (S := Zq q) (A := ℚ) fun x => by
      conv_rhs => rw [RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq]
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Ideal.span {(q : ℤ)}).primeCompl (Zq q) ℚ

noncomputable def residueFieldEquivZMod :
    IsLocalRing.ResidueField (Zq q) ≃+* ZMod q :=
  haveI : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (Nat.prime_iff_prime_int.mp (Fact.out (p := q.Prime))).irreducible
  ((RingEquiv.ofBijective _
    ((Ideal.span {(q : ℤ)}).bijective_algebraMap_quotient_residueField)).symm).trans
    (Int.quotientSpanNatEquivZMod q)

theorem residue_natCast_ne_zero {n : ℕ} (h : ¬ q ∣ n) :
    ((n : ℕ) : IsLocalRing.ResidueField (Zq q)) ≠ 0 := by
  intro h0
  apply h
  have h1 := congrArg (residueFieldEquivZMod q) h0
  rw [map_natCast, map_zero] at h1
  exact (CharP.cast_eq_zero_iff (ZMod q) q n).mp h1

end Instantiation

section GoodReduction

theorem valuation_eq_one_of_isUnit {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
    (r : A) (hr : IsUnit r) :
    valuation L (IsDiscreteValuationRing.maximalIdeal A) (algebraMap A L r) = 1 := by
  rcases lt_or_eq_of_le
      ((IsDiscreteValuationRing.maximalIdeal A).valuation_le_one (K := L) r) with h | h
  · exact absurd ((IsDiscreteValuationRing.maximalIdeal A).valuation_lt_one_iff_mem
      (K := L) r |>.mp h) (fun hm => (mem_nonunits_iff.mp
        ((IsLocalRing.mem_maximalIdeal r).mp hm)) hr)
  · exact h

theorem hasGoodReduction_of_valuation_Δ_eq_one {A : Type} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
    (V : WeierstrassCurve L) [V.IsIntegral A]
    (hΔ : valuation L (IsDiscreteValuationRing.maximalIdeal A) V.Δ = 1) :
    V.HasGoodReduction A := by
  have hMin : V.IsMinimal A := by
    refine ⟨⟨by simpa using (inferInstance : V.IsIntegral A), ?_⟩⟩
    intro C _ _
    have hle := (valuation_Δ_aux A (C • V)).2
    have heq : ((valuation_Δ_aux A ((1 : VariableChange L) • V)) :
        WithZero (Multiplicative ℤ)) = 1 := by
      rw [one_smul, valuation_Δ_aux_eq_of_isIntegral A V]
      exact hΔ
    exact Subtype.coe_le_coe.mp (by rw [heq]; exact hle)
  exact { toIsMinimal := hMin, goodReduction := hΔ }

variable (q : ℕ) [Fact q.Prime] (W : WeierstrassCurve ℤ)

theorem map_isIntegral : (W.map (Int.castRingHom ℚ)).IsIntegral (Zq q) := by
  refine isIntegral_of_exists_lift (Zq q)
    ⟨algebraMap ℤ _ W.a₁, ?_⟩ ⟨algebraMap ℤ _ W.a₂, ?_⟩ ⟨algebraMap ℤ _ W.a₃, ?_⟩
    ⟨algebraMap ℤ _ W.a₄, ?_⟩ ⟨algebraMap ℤ _ W.a₆, ?_⟩ <;>
  · rw [algebraMap_Zq_int]
    simp

theorem map_valuation_Δ (hΔ : ¬ (q : ℤ) ∣ W.Δ) :
    valuation ℚ (IsDiscreteValuationRing.maximalIdeal (Zq q)) (W.map (Int.castRingHom ℚ)).Δ
      = 1 := by
  have hu : IsUnit (algebraMap ℤ (Zq q) W.Δ) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Zq q)
      (Ideal.span {(q : ℤ)}) W.Δ).mpr
      (fun hmem => hΔ (Ideal.mem_span_singleton.mp hmem))
  have h : (W.map (Int.castRingHom ℚ)).Δ = algebraMap (Zq q) ℚ (algebraMap ℤ _ W.Δ) := by
    rw [map_Δ, algebraMap_Zq_int, eq_intCast]
  rw [h]
  exact valuation_eq_one_of_isUnit _ hu

theorem map_hasGoodReduction (hΔ : ¬ (q : ℤ) ∣ W.Δ) :
    (W.map (Int.castRingHom ℚ)).HasGoodReduction (Zq q) :=
  haveI := map_isIntegral q W
  hasGoodReduction_of_valuation_Δ_eq_one _ (map_valuation_Δ q W hΔ)

theorem reduction_map_eq [(W.map (Int.castRingHom ℚ)).IsMinimal (Zq q)] :
    reduction (Zq q) (W.map (Int.castRingHom ℚ)) =
      W.map (Int.castRingHom (IsLocalRing.ResidueField (Zq q))) := by
  have hinj : Function.Injective (algebraMap (Zq q) ℚ) := IsFractionRing.injective _ _
  have h1 : integralModel (Zq q) (W.map (Int.castRingHom ℚ))
      = W.map (algebraMap ℤ (Zq q)) := by
    ext <;> apply hinj
    · rw [integralModel_a₁_eq, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₁,
        algebraMap_Zq_int, eq_intCast]
    · rw [integralModel_a₂_eq, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₂,
        algebraMap_Zq_int, eq_intCast]
    · rw [integralModel_a₃_eq, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₃,
        algebraMap_Zq_int, eq_intCast]
    · rw [integralModel_a₄_eq, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₄,
        algebraMap_Zq_int, eq_intCast]
    · rw [integralModel_a₆_eq, WeierstrassCurve.map_a₆, WeierstrassCurve.map_a₆,
        algebraMap_Zq_int, eq_intCast]
  unfold reduction
  rw [h1, map_map]
  congr 1
  exact RingHom.ext_int _ _

end GoodReduction

section Count

def pointEquivOption {F : Type} [Field F] (V : WeierstrassCurve.Affine F) :
    V.Point ≃ Option {p : F × F // V.Nonsingular p.1 p.2} where
  toFun P := match P with
    | .zero => none
    | .some x y h => some ⟨(x, y), h⟩
  invFun o := match o with
    | none => .zero
    | some ⟨(x, y), h⟩ => .some x y h
  left_inv P := by cases P <;> rfl
  right_inv o := by rcases o with _ | ⟨⟨x, y⟩, h⟩ <;> rfl

theorem card_point_map_eq_of_ringEquiv {A B : Type} [Field A] [Field B] (e : A ≃+* B)
    (W : WeierstrassCurve ℤ) :
    Nat.card (W.map (Int.castRingHom A)).toAffine.Point =
      Nat.card (W.map (Int.castRingHom B)).toAffine.Point := by
  have hcurve : (W.map (Int.castRingHom A)).map e.toRingHom = W.map (Int.castRingHom B) := by
    rw [map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hiff : ∀ p : A × A, (W.map (Int.castRingHom A)).toAffine.Nonsingular p.1 p.2 ↔
      (W.map (Int.castRingHom B)).toAffine.Nonsingular (e p.1) (e p.2) := by
    intro p
    rw [← hcurve]
    exact ((W.map (Int.castRingHom A)).toAffine.map_nonsingular e.injective p.1 p.2).symm
  exact Nat.card_congr ((pointEquivOption _).trans ((Equiv.optionCongr
    (Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv) (fun p => hiff p))).trans
      (pointEquivOption _).symm))

end Count

theorem card_dvd_card_reduction (W : WeierstrassCurve ℤ) {p : ℕ} (hp : p.Prime)
    (hΔ : ¬ (p : ℤ) ∣ W.Δ) {n : ℕ} (hn : ¬ p ∣ n)
    (H : AddSubgroup (W.map (Int.castRingHom ℚ)).toAffine.Point) (hH : ∀ P ∈ H, n • P = 0) :
    Nat.card H ∣ Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hgood := map_hasGoodReduction p W hΔ
  let φ : (W.map (Int.castRingHom ℚ)).toAffine.Point →+
      (reduction (Zq p) (W.map (Int.castRingHom ℚ))).toAffine.Point :=
    AddMonoidHom.mk' (WeierstrassCurve.reducePoint_alt (Zq p) (W.map (Int.castRingHom ℚ)))
      (WeierstrassCurve.reducePoint_add (Zq p) (W.map (Int.castRingHom ℚ)))
  have hnres : ((n : ℕ) : IsLocalRing.ResidueField (Zq p)) ≠ 0 := residue_natCast_ne_zero p hn
  have hinj : Function.Injective (φ.comp H.subtype) := by
    intro P P' h
    have hsub : φ ((P : (W.map (Int.castRingHom ℚ)).toAffine.Point)
        - (P' : (W.map (Int.castRingHom ℚ)).toAffine.Point)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact h
    have htor : n • ((P : (W.map (Int.castRingHom ℚ)).toAffine.Point)
        - (P' : (W.map (Int.castRingHom ℚ)).toAffine.Point)) = 0 := by
      rw [nsmul_sub, hH _ P.2, hH _ P'.2, sub_zero]
    have hPQ := WeierstrassCurve.eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero (Zq p)
      (W.map (Int.castRingHom ℚ)) hnres _ htor hsub
    exact Subtype.ext (by rwa [sub_eq_zero] at hPQ)
  have h1 : Nat.card H ∣ Nat.card (reduction (Zq p) (W.map (Int.castRingHom ℚ))).toAffine.Point :=
    AddSubgroup.card_dvd_of_injective (φ.comp H.subtype) hinj
  have hcard : Nat.card (reduction (Zq p) (W.map (Int.castRingHom ℚ))).toAffine.Point
      = Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point := by
    rw [reduction_map_eq p W]
    exact card_point_map_eq_of_ringEquiv (residueFieldEquivZMod p) W
  exact hcard ▸ h1

end M4cP1Torsion
p2m_reactivate "P2MW.S_WeierstrassCurve_card_dvd_card_reduction_of_nsmul_eq_zero.M4cP1Torsion"

theorem solution (W : WeierstrassCurve ℤ) {p : ℕ} (hp : p.Prime) (hΔ : ¬ (p : ℤ) ∣ W.Δ) {V : WeierstrassCurve.Affine ℚ} (hV : W.map (Int.castRingHom ℚ) = V) {n : ℕ} (hn : ¬ p ∣ n) (H : AddSubgroup V.Point) (hH : ∀ P ∈ H, n • P = 0) : Nat.card H ∣ Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  subst hV
  exact M4cP1Torsion.card_dvd_card_reduction W hp hΔ hn H hH

end S_WeierstrassCurve_card_dvd_card_reduction_of_nsmul_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_card_dvd_card_reduction_of_nsmul_eq_zero (solution)
