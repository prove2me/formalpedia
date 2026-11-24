-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_transcendental_div_d53045909a4d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:24.473412+00:00
-- url     : https://prove2.me/submissions/9cae9824-7373-488c-8ab8-226977770be4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_LineField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_xL_ne_zero_6abe86b3f4b0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution {i j : Fin 2} (hij : i ≠ j) : Transcendental ℚ (xL i / xL j) := by
  rw [transcendental_iff_injective, injective_iff_map_eq_zero]
  intro p hp
  set n := p.natDegree
  set Q : MvPolynomial (Fin 2) ℚ :=
    ∑ k ∈ Finset.range (n + 1), C (p.coeff k) * X i ^ k * X j ^ (n - k) with hQdef
  have hQ : algebraMap _ L Q = xL j ^ n * Polynomial.aeval (xL i / xL j) p := by
    rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum, hQdef, map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hpow : xL j ^ n = xL j ^ (n - k) * xL j ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk']
    rw [map_mul, map_mul, map_pow, map_pow, hpow, Algebra.smul_def, div_pow]
    rw [show algebraMap (MvPolynomial (Fin 2) ℚ) L (C (p.coeff k)) = algebraMap ℚ L (p.coeff k) from
      (IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin 2) ℚ) L _).symm]
    have hj : xL j ^ k ≠ 0 := pow_ne_zero _ (xL_ne_zero j)
    change _ * xL i ^ k * xL j ^ (n - k) = _
    field_simp
  have hQ0 : Q = 0 := by
    apply IsFractionRing.injective (MvPolynomial (Fin 2) ℚ) L
    rw [hQ, hp, mul_zero, map_zero]
  have hev : MvPolynomial.aeval (fun m : Fin 2 => if m = i then (Polynomial.X : Polynomial ℚ) else 1) Q = p := by
    conv_rhs => rw [p.as_sum_range_C_mul_X_pow]
    rw [hQdef, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hij.symm, Polynomial.algebraMap_eq]
  rw [← hev, hQ0, map_zero]
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
