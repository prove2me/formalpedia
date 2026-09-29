-- Prove2me | solution 1 for WeierstrassCurve.Affine.CoordinateRing.isUnit_iff_eq_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/1dc7f5cf-9e72-5e66-acfc-1640fe9f6bc4

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isUnit_iff_eq_algebraMap

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

theorem solution {F : Type*} [Field F] {W : WeierstrassCurve F} (f : W.toAffine.CoordinateRing) : IsUnit f ↔ ∃ c : F, c ≠ 0 ∧ f = algebraMap F W.toAffine.CoordinateRing c := by
  constructor
  · intro hf
    obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq f
    have hnu : IsUnit (Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing) +
        q • CoordinateRing.mk W.toAffine Y)) := hf.map _
    have hdeg := Polynomial.degree_eq_zero_of_isUnit hnu
    rw [CoordinateRing.degree_norm_smul_basis] at hdeg

    have hq : q = 0 := by
      by_contra hq
      have h3 : (2 • q.degree + 3 : WithBot ℕ) = ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hq]
        norm_cast
      have hle : ((2 * q.natDegree + 3 : ℕ) : WithBot ℕ) ≤ (0 : WithBot ℕ) := by
        rw [← h3, ← hdeg]
        exact le_max_right _ _
      have hle' : 2 * q.natDegree + 3 ≤ 0 := by exact_mod_cast hle
      omega
    subst hq
    rw [zero_smul, add_zero] at hnu ⊢

    have hnp : Algebra.norm F[X] (p • (1 : W.toAffine.CoordinateRing)) = p ^ 2 := by
      have := CoordinateRing.norm_smul_basis (W' := W.toAffine) p 0
      rw [zero_smul, add_zero] at this
      rw [this]
      ring
    rw [hnp, isUnit_pow_iff two_ne_zero, Polynomial.isUnit_iff] at hnu
    obtain ⟨c, hc, rfl⟩ := hnu
    refine ⟨c, hc.ne_zero, ?_⟩
    rw [CoordinateRing.smul, mul_one]
    rfl
  · rintro ⟨c, hc, rfl⟩
    exact (IsUnit.mk0 c hc).map _

end S_WeierstrassCurve_Affine_CoordinateRing_isUnit_iff_eq_algebraMap
end P2MW
export P2MW.S_WeierstrassCurve_Affine_CoordinateRing_isUnit_iff_eq_algebraMap (solution)
