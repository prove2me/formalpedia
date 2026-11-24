-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_homogForm_mem_orbitIdeal_fdc7dade412e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:56.904123+00:00
-- url     : https://prove2.me/submissions/5f5d5e91-8d4a-4d68-8b73-cfa0645246fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_homog_sum_eq_99e15293109e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
variable {ι : Type} {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution [Fintype ι] [DecidableEq ι] (x : Cone n (AlgebraicClosure ℚ)) (g : Polynomial ℤ)
    (p q : Coord n) (hpq : p.1 = q.1) (hq : flatCone x q ≠ 0)
    (hg : Polynomial.aeval (flatCone x p / flatCone x q) g = 0) :
    homogForm g p q ∈ orbitIdeal x := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker]
  set y := flatCone x
  have key : ∀ j ∈ Finset.range (g.natDegree + 1),
      Geo.mConeMap (ι := blockIdx n) y (C (g.coeff j) * X p ^ j * X q ^ (g.natDegree - j)) =
        MvPolynomial.C ((g.coeff j : AlgebraicClosure ℚ) * y p ^ j * y q ^ (g.natDegree - j)) *
          MvPolynomial.X q.1 ^ g.natDegree := by
    intro j hj
    have hj' : j ≤ g.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have e : (MvPolynomial.X q.1 : MvPolynomial ι (AlgebraicClosure ℚ)) ^ g.natDegree =
        MvPolynomial.X q.1 ^ j * MvPolynomial.X q.1 ^ (g.natDegree - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hj']
    simp only [Geo.mConeMap, map_mul, map_pow, aeval_X, e, hpq, eq_intCast, map_intCast]
    ring
  rw [homogForm, map_sum, Finset.sum_congr rfl key, ← Finset.sum_mul, ← map_sum,
    homog_sum_eq g _ _ hq]
  simp only [y] at hg ⊢
  simp only [map_mul, mul_eq_zero]
  exact Or.inl (Or.inr (MvPolynomial.C_eq_zero.mpr (by
    rw [Polynomial.aeval_def] at hg ⊢
    convert hg using 2
    exact RingHom.ext_int _ _)))
end GroundTheory.Heights₂.Heights
