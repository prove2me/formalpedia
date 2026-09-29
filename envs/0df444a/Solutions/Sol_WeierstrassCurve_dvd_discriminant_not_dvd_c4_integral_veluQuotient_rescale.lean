-- Prove2me | solution 1 for WeierstrassCurve.dvd_discriminant_not_dvd_c4_integral_veluQuotient_rescale
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/d2310be5-da59-5fc0-83ff-25b3488c5080

import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_ValuationSubring_valuation_intCast_eq_one_of_not_dvd
import Theorems.Thm_ValuationSubring_valuation_intCast_lt_one_of_dvd
import Theorems.Thm_ValuationSubring_valuation_natCast_eq_one_of_not_dvd
import Theorems.Thm_WeierstrassCurve_valuation_veluQuotient_oddOrderSummingSet_c4_of_multiplicative
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
import Theorems.Thm_WeierstrassCurve_valuation_prod_veluU_oddOrderSummingSet_of_multiplicative
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_dvd_discriminant_not_dvd_c4_integral_veluQuotient_rescale
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.veluY_empty"

open WeierstrassCurve WeierstrassCurve.Affine ValuationSubring

private lemma eq_one_of_pow_eq_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {a : Γ} {n : ℕ} (hn : n ≠ 0) (h : a ^ n = 1) : a = 1 := by
  rcases lt_trichotomy a 1 with hlt | heq | hgt
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' hlt hn))
  · exact heq
  · exact absurd h.symm (ne_of_lt (one_lt_pow₀ hgt hn))

private lemma lt_one_of_pow_lt_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {a : Γ} {n : ℕ} (hn : n ≠ 0) (h : a ^ n < 1) : a < 1 := by
  rcases lt_trichotomy a 1 with hlt | heq | hgt
  · exact hlt
  · exact absurd h (by rw [heq, one_pow]; exact lt_irrefl 1)
  · exact absurd h (not_lt.mpr (one_lt_pow₀ hgt hn).le)

private lemma baseChange_Δ_intCast (W : WeierstrassCurve ℤ) :
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Δ
      = ((W.Δ : ℤ) : AlgebraicClosure ℚ) := by
  show ((W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ = _
  rw [map_Δ, map_Δ]; simp

private lemma baseChange_c₄_intCast (W : WeierstrassCurve ℤ) :
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).c₄
      = ((W.c₄ : ℤ) : AlgebraicClosure ℚ) := by
  show ((W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))).c₄ = _
  rw [map_c₄, map_c₄]; simp

theorem solution
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQord : addOrderOf Q = p)
    (W' : WeierstrassCurve ℤ) (u : (AlgebraicClosure ℚ)ˣ)
    (hW' : (W'.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) =
      (⟨u, 0, 0, 0⟩ : VariableChange (AlgebraicClosure ℚ)) •
        (let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
         Wb.veluQuotient (Wb.oddOrderSummingSet Q (p / 2))))
    (hu : ∃ k : ℤ, (u : AlgebraicClosure ℚ) ^ 12 = (p : AlgebraicClosure ℚ) ^ k)
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (hqΔ : (q : ℤ) ∣ W.Δ) (hqc₄ : ¬ (q : ℤ) ∣ W.c₄) :
    (q : ℤ) ∣ W'.Δ ∧ ¬ (q : ℤ) ∣ W'.c₄ := by
  haveI : CharZero (AlgebraicClosure ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective

  simp only at hW'
  set V := ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluQuotient
    (((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (p / 2)) with hV

  obtain ⟨A, hA, -⟩ := ValuationSubring.exists_isFrobeniusAt_rat q hq
  have hvq : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := hA

  have hvu : A.valuation (u : AlgebraicClosure ℚ) = 1 := by
    obtain ⟨k, hk⟩ := hu
    have hqdp : ¬ q ∣ p := fun hd => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp hd)
    have hvp : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) = 1 :=
      A.valuation_natCast_eq_one_of_not_dvd hq hvq hqdp
    refine eq_one_of_pow_eq_one (n := 12) (by norm_num) ?_
    rw [← map_pow, hk, map_zpow₀, hvp, one_zpow]
  have hvuinv : A.valuation (↑u⁻¹ : AlgebraicClosure ℚ) = 1 := by
    rw [← inv_eq_one, ← map_inv₀, ← Units.val_inv_eq_inv_val, inv_inv]
    exact hvu

  haveI hWbE : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).IsElliptic := by
    rw [isElliptic_iff]
    refine isUnit_iff_ne_zero.mpr ?_
    show ((W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ))).Δ ≠ 0
    rw [map_Δ, map_Δ]
    exact (map_ne_zero _).mpr ((map_ne_zero_iff _ Int.cast_injective).mpr hΔ)
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hord' : addOrderOf Q = 2 * (p / 2) + 1 := by rw [hQord]; omega
  have hp2n1 : 2 * (p / 2) + 1 = p := by omega

  have hΔW' : A.valuation ((W'.Δ : ℤ) : AlgebraicClosure ℚ) = A.valuation V.Δ := by
    have h1 := congrArg WeierstrassCurve.Δ hW'
    rw [baseChange_Δ_intCast, variableChange_Δ] at h1
    rw [h1, map_mul, map_pow, hvuinv, one_pow, one_mul]
  have hc₄W' : A.valuation ((W'.c₄ : ℤ) : AlgebraicClosure ℚ) = A.valuation V.c₄ := by
    have h1 := congrArg WeierstrassCurve.c₄ hW'
    rw [baseChange_c₄_intCast, variableChange_c₄] at h1
    rw [h1, map_mul, map_pow, hvuinv, one_pow, one_mul]

  have hvVc₄ : A.valuation V.c₄ = 1 :=
    WeierstrassCurve.valuation_veluQuotient_oddOrderSummingSet_c4_of_multiplicative
      W hΔ hq hqΔ hqc₄ A hA hp hp2 hqp Q hQord

  have hvWΔ : A.valuation ((W.Δ : ℤ) : AlgebraicClosure ℚ) < 1 :=
    A.valuation_intCast_lt_one_of_dvd hvq hqΔ
  have hvWΔne : A.valuation ((W.Δ : ℤ) : AlgebraicClosure ℚ) ≠ 0 := by
    rw [ne_eq, Valuation.zero_iff]
    exact Int.cast_ne_zero.mpr hΔ

  have hID : A.valuation V.Δ *
      A.valuation (∏ P ∈ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q
        (p / 2), ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).veluU P.1 P.2) ^ 4
        = A.valuation ((W.Δ : ℤ) : AlgebraicClosure ℚ) ^ p := by
    have h := WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow
      (F := AlgebraicClosure ℚ) ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)) Q hord'
    rw [hp2n1] at h
    have h' := congrArg A.valuation h
    rw [map_mul, map_pow, map_pow, baseChange_Δ_intCast] at h'
    exact h'

  have hvVΔ : A.valuation V.Δ < 1 := by
    have hnode := WeierstrassCurve.valuation_prod_veluU_oddOrderSummingSet_of_multiplicative
      W hΔ hq hqΔ hqc₄ A hA hp hp2 hqp Q hQord
    simp only at hnode
    by_cases hQ0 : W.InZeroComponentAt A Q
    ·
      rw [hnode.1 hQ0, one_pow, mul_one] at hID
      rw [hID]
      exact pow_lt_one₀ zero_le' hvWΔ hp.ne_zero
    ·

      have hprodp := hnode.2 hQ0

      have h2 := congrArg (· ^ p) hID
      rw [mul_pow, ← pow_mul, ← pow_mul, hprodp] at h2

      have hexp : p * p = 1 + (p ^ 2 - 1) := by
        have hpp : p ^ 2 = p * p := sq p
        have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
        omega
      rw [hexp, pow_add, pow_one] at h2
      have h3 : A.valuation V.Δ ^ p = A.valuation ((W.Δ : ℤ) : AlgebraicClosure ℚ) :=
        mul_right_cancel₀ (pow_ne_zero _ hvWΔne) h2
      exact lt_one_of_pow_lt_one hp.ne_zero (h3 ▸ hvWΔ)

  refine ⟨?_, ?_⟩
  · by_contra hnd
    have h1 : A.valuation ((W'.Δ : ℤ) : AlgebraicClosure ℚ) = 1 :=
      A.valuation_intCast_eq_one_of_not_dvd hq hvq hnd
    rw [hΔW'] at h1
    exact (ne_of_lt hvVΔ) h1
  · intro hd
    have h1 : A.valuation ((W'.c₄ : ℤ) : AlgebraicClosure ℚ) < 1 :=
      A.valuation_intCast_lt_one_of_dvd hvq hd
    rw [hc₄W', hvVc₄] at h1
    exact lt_irrefl 1 h1

end S_WeierstrassCurve_dvd_discriminant_not_dvd_c4_integral_veluQuotient_rescale
end P2MW
export P2MW.S_WeierstrassCurve_dvd_discriminant_not_dvd_c4_integral_veluQuotient_rescale (solution)
