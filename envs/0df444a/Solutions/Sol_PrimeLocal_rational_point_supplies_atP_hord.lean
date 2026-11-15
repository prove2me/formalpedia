-- Prove2me | solution 1 for PrimeLocal.rational_point_supplies_atP_hord
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:22:52.699458+00:00
-- url     : https://prove2.me/submissions/9951525b-7c10-4d48-8ab2-7a7ff63beecf

import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Theorems.Thm_MazurReduction_odd_prime_division_nonzero
import Theorems.Thm_ValuationSubring_algebraMap_rat_mem_iff_of_liesOverPrime
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal
universe u v

namespace PrimeLocal
/-- Rational odd-prime torsion has integral abscissa at every place above that prime. -/
theorem _root_.solution (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (x y : ℚ) (h : (W.map (Int.castRingHom ℚ)).toAffine.Nonsingular x y) (hP : addOrderOf (WeierstrassCurve.Affine.Point.some x y h) = p) : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p → ∃ (x' y' : AlgebraicClosure ℚ) (h' : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular x' y'), p • (Point.some x' y' h') = 0 ∧ x' ∈ A := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let V := (Rat.padicValuation p).valuationSubring
  let Wv : WeierstrassCurve V := W.map (Int.castRingHom V)
  have hmap : Wv.map V.subtype = W.map (Int.castRingHom ℚ) := by
    simp only [Wv, WeierstrassCurve.map_map, RingHom.eq_intCast']
  have hpzero : p • Point.some x y h = 0 := by
    rw [← hP]
    exact addOrderOf_nsmul_eq_zero _
  have hx : x ∈ V := by
    by_contra hx
    have heq : (Wv.map V.subtype).toAffine.Equation x y := by rw [hmap]; exact h.1
    have hn := MazurReduction.odd_prime_division_nonzero p (by omega) Wv heq hx
    have hE : (W.map (Int.castRingHom ℚ)).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr (by rw [WeierstrassCurve.map_Δ]; change (W.Δ : ℚ) ≠ 0; exact_mod_cast hΔ)⟩
    letI := hE
    apply hn
    rw [hmap]
    exact (Point.nsmul_some_eq_zero_iff_eval_prePsi _ (hp.odd_of_ne_two (by omega)) h).mp hpzero
  intro A hA
  have hh : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).toAffine.Nonsingular (algebraMap ℚ (AlgebraicClosure ℚ) x) (algebraMap ℚ (AlgebraicClosure ℚ) y) :=
    ((W.map (Int.castRingHom ℚ)).toAffine.baseChange_nonsingular
      (f := Algebra.ofId ℚ (AlgebraicClosure ℚ))
      (Algebra.ofId ℚ (AlgebraicClosure ℚ)).injective x y).mpr h
  refine ⟨algebraMap ℚ (AlgebraicClosure ℚ) x, algebraMap ℚ (AlgebraicClosure ℚ) y, hh, ?_, ?_⟩
  · change p • Point.baseChange (W' := (W.map (Int.castRingHom ℚ)).toAffine)
      ℚ (AlgebraicClosure ℚ) (Point.some x y h) = 0
    exact (map_nsmul (Point.baseChange (W' := (W.map (Int.castRingHom ℚ)).toAffine)
      ℚ (AlgebraicClosure ℚ)) p _).symm.trans
      ((congrArg (Point.baseChange (W' := (W.map (Int.castRingHom ℚ)).toAffine)
        ℚ (AlgebraicClosure ℚ)) hpzero).trans (_root_.map_zero _))
  · exact (ValuationSubring.algebraMap_rat_mem_iff_of_liesOverPrime A hA x).mpr hx
end PrimeLocal
