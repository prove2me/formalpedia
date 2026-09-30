-- Prove2me | solution 1 for WeierstrassEllipticZeta.hasSumLocallyUniformly_zetaSeries
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-05T00:00:21.551215+00:00
-- url     : https://prove2.me/submissions/a5da1ad6-5f08-48b2-a0da-b4e135fd6e04

import Definitions.Def_WeierstrassEllipticZeta_Defs

/-!
Analytic foundations for the canonical lattice-series zeta function.

The normalization and analytic identities are those of NIST DLMF §23.2,
https://dlmf.nist.gov/23.2 (equations 23.2.5 and 23.2.7).
The convergence proof uses a cubic tail bound and Mathlib's lattice summability.
-/

noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

/-- Cubic decay of the regularized zeta summand, uniformly on a bounded disk. -/
lemma zetaSummand_bound (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ‖z‖ < r)
    (l : ℂ) (hl : 2 * r ≤ ‖l‖) :
    ‖1 / (z - l) + 1 / l + z / l ^ 2‖ ≤ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ) := by
  have hlpos : 0 < ‖l‖ := by linarith
  have hlne : l ≠ 0 := norm_pos_iff.mp hlpos
  have hzl : z - l ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    subst z
    linarith
  have hnorm : ‖l‖ / 2 ≤ ‖z - l‖ := by
    rw [norm_sub_rev]
    exact le_trans (by linarith) (norm_sub_norm_le l z)
  calc
    _ = ‖z ^ 2 / (l ^ 2 * (z - l))‖ := by
      congr 1
      field_simp
      ring
    _ = ‖z‖ ^ 2 / (‖l‖ ^ 2 * ‖z - l‖) := by simp
    _ ≤ r ^ 2 / (‖l‖ ^ 2 * (‖l‖ / 2)) := by gcongr
    _ = 2 * r ^ 2 / ‖l‖ ^ 3 := by field
    _ = _ := by norm_cast

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution (L : PeriodPair) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : ℂ) ↦ if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2)
      (fun z ↦ ∑' l : L.lattice, if l = 0 then 0 else
        1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2) := by
  refine L.hasSumLocallyUniformly_aux (u := fun r l ↦ 2 * r ^ 2 * ‖l‖ ^ (-3 : ℝ)) _
    (fun _ _ ↦ (ZLattice.summable_norm_rpow _ _ (by simp; norm_num)).mul_left _)
    fun r hr ↦ Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h z hz l rfl
  split_ifs
  · simp only [norm_zero]
    positivity
  · exact zetaSummand_bound r hr z hz l h
