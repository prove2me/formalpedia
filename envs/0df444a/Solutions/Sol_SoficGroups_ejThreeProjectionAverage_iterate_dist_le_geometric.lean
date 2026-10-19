-- Prove2me | solution 1 for SoficGroups.ejThreeProjectionAverage_iterate_dist_le_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.835808+00:00
-- url     : https://prove2.me/submissions/22be1be9-77c2-4027-bff0-59d58be196b3

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejThreeResidualEnergy_nonneg
import Theorems.Thm_SoficGroups_ejThreeProjectionAverage_dist_sq_le
import Theorems.Thm_SoficGroups_ejThreeResidualEnergy_iterate_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
namespace SoficGroups
theorem _root_.solution
    (δ : ℝ) (hδ : δ ≤ 3)
    (hgap : ∀ x : H,
      δ * ejThreeResidualEnergy V x ≤ ‖ejThreeResidualMap V x‖ ^ 2)
    (x : H) (n : ℕ) :
    dist (((ejThreeProjectionAverage V : H → H)^[n]) x)
        (((ejThreeProjectionAverage V : H → H)^[n + 1]) x) ≤
      Real.sqrt (ejThreeResidualEnergy V x / 3) *
        (1 - δ / 6) ^ n := by
  let q : ℝ := 1 - δ / 3
  let r : ℝ := 1 - δ / 6
  have hq : 0 ≤ q := by
    dsimp [q]
    linarith
  have hr : 0 ≤ r := by
    dsimp [r]
    linarith
  have hqr : q ≤ r ^ 2 := by
    dsimp [q, r]
    nlinarith [sq_nonneg δ]
  let y : H := ((ejThreeProjectionAverage V : H → H)^[n]) x
  have hiter :
      ejThreeResidualEnergy V y ≤
        q ^ n * ejThreeResidualEnergy V x :=
    ejThreeResidualEnergy_iterate_le V δ hδ hgap x n
  have hpow : q ^ n ≤ (r ^ 2) ^ n :=
    pow_le_pow_left₀ hq hqr n
  have henergy :
      ejThreeResidualEnergy V y ≤
        r ^ (2 * n) * ejThreeResidualEnergy V x := by
    calc
      ejThreeResidualEnergy V y ≤
          q ^ n * ejThreeResidualEnergy V x := hiter
      _ ≤ (r ^ 2) ^ n * ejThreeResidualEnergy V x :=
        mul_le_mul_of_nonneg_right hpow
          (ejThreeResidualEnergy_nonneg V x)
      _ = r ^ (2 * n) * ejThreeResidualEnergy V x := by
        rw [pow_mul]
  have hstep := ejThreeProjectionAverage_dist_sq_le V y
  have hsqrt :
      (Real.sqrt (ejThreeResidualEnergy V x / 3)) ^ 2 =
        ejThreeResidualEnergy V x / 3 :=
    Real.sq_sqrt
      (div_nonneg (ejThreeResidualEnergy_nonneg V x) (by norm_num))
  have hsquared :
      dist y (ejThreeProjectionAverage V y) ^ 2 ≤
        (Real.sqrt (ejThreeResidualEnergy V x / 3) * r ^ n) ^ 2 := by
    rw [mul_pow, hsqrt]
    have hpower : (r ^ n) ^ 2 = r ^ (2 * n) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hpower]
    nlinarith
  have hdist :
      dist y (ejThreeProjectionAverage V y) ≤
        Real.sqrt (ejThreeResidualEnergy V x / 3) * r ^ n :=
    (sq_le_sq₀ (dist_nonneg) (by positivity)).mp hsquared
  change dist y
    (((ejThreeProjectionAverage V : H → H)^[n + 1]) x) ≤
      Real.sqrt (ejThreeResidualEnergy V x / 3) * r ^ n
  rw [Function.iterate_succ_apply']
  exact hdist
end SoficGroups
