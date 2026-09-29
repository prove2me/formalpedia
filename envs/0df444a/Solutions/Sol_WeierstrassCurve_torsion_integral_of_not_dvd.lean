-- Prove2me | solution 1 for WeierstrassCurve.torsion_integral_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/8795c035-8685-592c-b5a7-9488845b0445

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.RingTheory.Valuation.ValuationSubring
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_ValuationSubring_valuation_natCast_eq_one_of_not_dvd
import Theorems.Thm_Valuation_map_eval_eq_pow_of_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_torsion_integral_of_not_dvd
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

p2m_open "WeierstrassCurve~evalEval_ψ_sq WeierstrassCurve.Affine WeierstrassCurve.Affine.Point"
open Polynomial
open scoped Polynomial.Bivariate

namespace TorsionIntegralPort

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

theorem baseChange_eq_map (W : WeierstrassCurve ℤ) :
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) : WeierstrassCurve (AlgebraicClosure ℚ))
      = W.map (Int.castRingHom (AlgebraicClosure ℚ)) := by
  show (W.map (Int.castRingHom ℚ)).map (algebraMap ℚ (AlgebraicClosure ℚ)) = _
  rw [WeierstrassCurve.map_map]
  congr 1

theorem a_mem (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₁ ∈ A ∧
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₂ ∈ A ∧
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₃ ∈ A ∧
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₄ ∈ A ∧
    ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).a₆ ∈ A := by
  have hE := baseChange_eq_map W
  simp only [Affine.baseChange] at hE ⊢
  rw [hE]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, eq_intCast]
  exact ⟨intCast_mem A _, intCast_mem A _, intCast_mem A _, intCast_mem A _, intCast_mem A _⟩

theorem valuation_coeff_ΨSq_le_one (W : WeierstrassCurve ℤ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (m : ℤ) (i : ℕ) :
    A.valuation ((((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) :
      WeierstrassCurve (AlgebraicClosure ℚ)).ΨSq m).coeff i) ≤ 1 := by
  rw [baseChange_eq_map W, map_ΨSq, Polynomial.coeff_map, eq_intCast]
  exact (A.valuation_le_one_iff _).mpr (intCast_mem A _)

noncomputable abbrev Ecurve (W : WeierstrassCurve ℤ) : WeierstrassCurve (AlgebraicClosure ℚ) :=
  ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ) : WeierstrassCurve (AlgebraicClosure ℚ))

end TorsionIntegralPort

open TorsionIntegralPort in
theorem solution (W : WeierstrassCurve ℤ) {q : ℕ} (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    {n : ℕ} (hqn : ¬ q ∣ n)
    (P : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (hP : n • P = 0) :
    P = 0 ∨ ∃ (x y : AlgebraicClosure ℚ)
        (h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x y),
      P = .some x y h ∧ x ∈ A ∧ y ∈ A := by
  rcases P with _ | ⟨x, y, h⟩
  · exact Or.inl rfl
  right
  refine ⟨x, y, h, rfl, ?_⟩
  have hq1 : A.valuation (q : AlgebraicClosure ℚ) < 1 := (A.mem_nonunits_iff).mp hA
  have hn0 : n ≠ 0 := fun h => hqn (h ▸ dvd_zero q)
  have hnQ : ((n : ℤ) : AlgebraicClosure ℚ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr hn0
  have ha : (Ecurve W).a₁ ∈ A ∧ (Ecurve W).a₂ ∈ A ∧ (Ecurve W).a₃ ∈ A ∧
      (Ecurve W).a₄ ∈ A ∧ (Ecurve W).a₆ ∈ A := a_mem W A
  have hΨSqcoeff : ∀ i : ℕ, A.valuation (((Ecurve W).ΨSq (n : ℤ)).coeff i) ≤ 1 :=
    fun i => valuation_coeff_ΨSq_le_one W A (n : ℤ) i

  have hz : (n : ℤ) • (Affine.Point.some x y h) = 0 := by
    rw [natCast_zsmul]; exact hP
  have hψ : ((Ecurve W).ψ (n : ℤ)).evalEval x y = 0 :=
    (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (Ecurve W) h (n : ℤ)).mp hz
  have hΨSq : ((Ecurve W).ΨSq (n : ℤ)).eval x = 0 := by
    have h2 := evalEval_ψ_sq (Ecurve W) h.1 (n : ℤ)
    rw [hψ, zero_pow two_ne_zero] at h2
    exact h2.symm
  have hvn : A.valuation (n : AlgebraicClosure ℚ) = 1 :=
    ValuationSubring.valuation_natCast_eq_one_of_not_dvd A hq hq1 hqn

  have hxA : x ∈ A := by
    by_contra hx
    have hx1 : 1 < A.valuation x :=
      not_le.mp (fun hle => hx (A.mem_of_valuation_le_one x hle))
    have hl : A.valuation ((Ecurve W).ΨSq (n : ℤ)).leadingCoeff = 1 := by
      rw [(Ecurve W).leadingCoeff_ΨSq hnQ]
      push_cast
      rw [map_pow, hvn, one_pow]
    have hval := Valuation.map_eval_eq_pow_of_one_lt A.valuation hΨSqcoeff hl hx1
    rw [hΨSq, _root_.map_zero] at hval
    exact pow_ne_zero _ ((zero_lt_one.trans hx1).ne') hval.symm
  refine ⟨hxA, ?_⟩

  by_contra hy
  obtain ⟨ha1, ha2, ha3, ha4, ha6⟩ := ha
  have hy1 : 1 < A.valuation y :=
    not_le.mp (fun hle => hy (A.mem_of_valuation_le_one y hle))
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy A.zero_mem
  have hyi : A.valuation y⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hy1
  have heqn := ((Ecurve W).toAffine.equation_iff x y).mp h.1
  set c : AlgebraicClosure ℚ := (Ecurve W).a₁ * x + (Ecurve W).a₃ with hc
  set d : AlgebraicClosure ℚ := x ^ 3 + (Ecurve W).a₂ * x ^ 2 + (Ecurve W).a₄ * x + (Ecurve W).a₆ with hd
  have hcA : c ∈ A := A.add_mem _ _ (A.mul_mem _ _ ha1 hxA) ha3
  have hdA : d ∈ A := by
    refine A.add_mem _ _ (A.add_mem _ _ (A.add_mem _ _ ?_ ?_) ?_) ha6
    · exact A.pow_mem hxA 3
    · exact A.mul_mem _ _ ha2 (A.pow_mem hxA 2)
    · exact A.mul_mem _ _ ha4 hxA
  have key : (1 : AlgebraicClosure ℚ) = d * y⁻¹ ^ 2 - c * y⁻¹ := by
    field_simp
    linear_combination heqn
  have hub : A.valuation (d * y⁻¹ ^ 2 - c * y⁻¹) < 1 := by
    refine lt_of_le_of_lt (A.valuation.map_sub _ _) (max_lt ?_ ?_)
    · rw [map_mul, map_pow]
      calc A.valuation d * A.valuation y⁻¹ ^ 2
          ≤ 1 * A.valuation y⁻¹ ^ 2 :=
            mul_le_mul' ((A.valuation_le_one_iff _).mpr hdA) le_rfl
        _ = A.valuation y⁻¹ * A.valuation y⁻¹ := by rw [one_mul, pow_two]
        _ ≤ 1 * A.valuation y⁻¹ := mul_le_mul' hyi.le le_rfl
        _ = A.valuation y⁻¹ := one_mul _
        _ < 1 := hyi
    · rw [map_mul]
      calc A.valuation c * A.valuation y⁻¹
          ≤ 1 * A.valuation y⁻¹ :=
            mul_le_mul' ((A.valuation_le_one_iff _).mpr hcA) le_rfl
        _ = A.valuation y⁻¹ := one_mul _
        _ < 1 := hyi
  rw [← key, _root_.map_one] at hub
  exact absurd hub (lt_irrefl 1)

end S_WeierstrassCurve_torsion_integral_of_not_dvd
end P2MW
export P2MW.S_WeierstrassCurve_torsion_integral_of_not_dvd (solution)
