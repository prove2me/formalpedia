-- Prove2me | solution 1 for WeierstrassCurve.eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8da5a49f-1077-5eb5-91d5-15d879c39ed0

import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_reducePoint_some_eq_zero_iff
import Definitions.Def_EllipticCurve_PointReduction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "WeierstrassCurve~evalEval_ψ_sq IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum"
open Polynomial
open scoped Polynomial.Bivariate

namespace TorsionInjectivity

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

theorem valuation_eval_of_pole {f : Polynomial K} {x : K}
    (hc : ∀ i, valuation K (IsDiscreteValuationRing.maximalIdeal R) (f.coeff i) ≤ 1)
    (hl : valuation K (IsDiscreteValuationRing.maximalIdeal R) f.leadingCoeff = 1)
    (hx : 1 < valuation K (IsDiscreteValuationRing.maximalIdeal R) x) :
    valuation K (IsDiscreteValuationRing.maximalIdeal R) (f.eval x)
      = valuation K (IsDiscreteValuationRing.maximalIdeal R) x ^ f.natDegree := by
  set v := valuation K (IsDiscreteValuationRing.maximalIdeal R) with hv
  have hx0 : v x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl' : v (f.coeff f.natDegree) = 1 := hl
  have htop : v (f.coeff f.natDegree * x ^ f.natDegree) = v x ^ f.natDegree := by
    rw [map_mul, map_pow, hl', one_mul]
  have hlower : v (∑ i ∈ Finset.range f.natDegree, f.coeff i * x ^ i)
      < v x ^ f.natDegree := by
    refine v.map_sum_lt (pow_ne_zero _ hx0) ?_
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc v (f.coeff i) * v x ^ i ≤ 1 * v x ^ i := mul_le_mul' (hc i) le_rfl
      _ = v x ^ i := one_mul _
      _ < v x ^ f.natDegree := pow_lt_pow_right₀ hx hi
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ,
    Valuation.map_add_eq_of_lt_right _ (htop ▸ hlower), htop]

theorem valuation_coeff_ΨSq_le_one (W : WeierstrassCurve K) [W.IsIntegral R] (n : ℤ) (i : ℕ) :
    valuation K (IsDiscreteValuationRing.maximalIdeal R) ((W.ΨSq n).coeff i) ≤ 1 := by
  have h : W.ΨSq n = ((integralModel R W).ΨSq n).map (algebraMap R K) := by
    conv_lhs => rw [← baseChange_integralModel_eq R W]
    exact map_ΨSq (integralModel R W) (algebraMap R K) n
  rw [h, Polynomial.coeff_map]
  exact valuation_le_one (IsDiscreteValuationRing.maximalIdeal R) _

theorem valuation_natCast_eq_one {n : ℕ} (hn : (n : ResidueField R) ≠ 0) :
    valuation K (IsDiscreteValuationRing.maximalIdeal R) (n : K) = 1 ∧ (n : K) ≠ 0 := by
  set v := valuation K (IsDiscreteValuationRing.maximalIdeal R) with hv
  have hmem : (n : R) ∉ IsLocalRing.maximalIdeal R := by
    intro hmem
    exact hn (by rw [← map_natCast (residue R) n]; exact (residue_eq_zero_iff _).mpr hmem)
  have hu : IsUnit (n : R) := by
    by_contra h
    exact hmem ((mem_maximalIdeal _).mpr h)
  obtain ⟨u, hu⟩ := hu
  have hnK : (n : K) = algebraMap R K (n : R) := by rw [map_natCast]
  have hprod : v (algebraMap R K (u : R)) * v (algebraMap R K ((u⁻¹ : Rˣ) : R)) = 1 := by
    rw [← v.map_mul, ← map_mul, Units.mul_inv, map_one, v.map_one]
  have h1 : v (algebraMap R K (u : R)) = 1 := by
    refine le_antisymm (valuation_le_one (IsDiscreteValuationRing.maximalIdeal R) _) ?_
    calc (1 : WithZero (Multiplicative ℤ))
          = v (algebraMap R K (u : R)) * v (algebraMap R K ((u⁻¹ : Rˣ) : R)) :=
          hprod.symm
      _ ≤ v (algebraMap R K (u : R)) * 1 :=
          mul_le_mul' le_rfl (valuation_le_one (IsDiscreteValuationRing.maximalIdeal R) _)
      _ = v (algebraMap R K (u : R)) := mul_one _
  have hveq : v (n : K) = 1 := by rw [hnK, ← hu]; exact h1
  refine ⟨hveq, fun h0 => ?_⟩
  rw [h0, v.map_zero] at hveq
  exact zero_ne_one hveq

theorem evalEval_ψ_sq {F : Type*} [Field F] (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Equation x y) (n : ℤ) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have h0 : W.toAffine.polynomial.eval₂ (evalRingHom x) y = 0 := by
    rw [eval₂_evalRingHom]; exact h
  let e : W.toAffine.CoordinateRing →+* F := AdjoinRoot.lift (evalRingHom x) y h0
  have he : ∀ p : F[X][Y], e (Affine.CoordinateRing.mk W p) = p.evalEval x y := fun p ↦ by
    show AdjoinRoot.lift (evalRingHom x) y h0 (AdjoinRoot.mk _ p) = _
    rw [AdjoinRoot.lift_mk, eval₂_evalRingHom]
  calc ((W.ψ n).evalEval x y) ^ 2
      = e (Affine.CoordinateRing.mk W (W.ψ n)) ^ 2 := by rw [he]
    _ = e (Affine.CoordinateRing.mk W (W.ψ n) ^ 2) := (map_pow e _ 2).symm
    _ = e (Affine.CoordinateRing.mk W (C (W.ΨSq n))) := by
        rw [Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
    _ = (C (W.ΨSq n)).evalEval x y := he _
    _ = (W.ΨSq n).eval x := evalEval_C x y _

end TorsionInjectivity

open TorsionInjectivity in

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [W.HasGoodReduction R] {n : ℕ} (hn : (n : IsLocalRing.ResidueField R) ≠ 0)
    (P : W.toAffine.Point) (hP : n • P = 0) (h0 : WeierstrassCurve.reducePoint_alt R W P = 0) :
    P = 0 := by
  cases P with
  | zero => rfl
  | some x y h =>
    exfalso
    have hx : ¬ valuation K (IsDiscreteValuationRing.maximalIdeal R) x ≤ 1 :=
      (WeierstrassCurve.reducePoint_some_eq_zero_iff R W h).mp h0
    have hx1 : 1 < valuation K (IsDiscreteValuationRing.maximalIdeal R) x := not_le.mp hx

    have hz : (n : ℤ) • (Affine.Point.some x y h) = 0 := by
      rw [natCast_zsmul]; exact hP
    have hψ : (W.ψ (n : ℤ)).evalEval x y = 0 :=
      (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W h (n : ℤ)).mp hz
    have hΨSq : (W.ΨSq (n : ℤ)).eval x = 0 := by
      have h2 := evalEval_ψ_sq W h.1 (n : ℤ)
      rw [hψ, zero_pow two_ne_zero] at h2
      exact h2.symm

    obtain ⟨hvn, hn0⟩ := valuation_natCast_eq_one R (K := K) hn
    have hnK : ((n : ℤ) : K) ≠ 0 := by push_cast; exact hn0
    have hl : valuation K (IsDiscreteValuationRing.maximalIdeal R)
        (W.ΨSq (n : ℤ)).leadingCoeff = 1 := by
      rw [W.leadingCoeff_ΨSq hnK]
      push_cast
      rw [map_pow, hvn, one_pow]
    have hval := valuation_eval_of_pole R
      (valuation_coeff_ΨSq_le_one R W (n : ℤ)) hl hx1
    rw [hΨSq, map_zero] at hval
    exact pow_ne_zero _ ((zero_lt_one.trans hx1).ne') hval.symm

end S_WeierstrassCurve_eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_eq_zero_of_smul_eq_zero_of_reducePoint_eq_zero (solution)
