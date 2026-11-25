-- Prove2me | solution 1 for OptimalAffinity.oa2x2_current_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:59:16.904614+00:00
-- url     : https://prove2.me/submissions/6f40365d-cc2e-45a2-8156-2c1cc0e51fc5

module
public import Definitions.Def_proofs_OptimalAffinity_Steady
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Theorems.Thm_OptimalAffinity_oa2x2_polynomialCertificate
public import Theorems.Thm_OptimalAffinity_oa2x2_current_formula
public import Theorems.Thm_OptimalAffinity_oa2x2_ySteady_iff


set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution
    (x y : ℝ) (hy : 0 < y) (hsteady : YSteady oa2x2 x y) :
    productionCurrent oa2x2 x y ≤ 1 := by
  rw [oa2x2_current_formula]
  have hsteady' := (oa2x2_ySteady_iff x y).mp hsteady
  have hzero : 3 * x - 2 * y - 7 * y ^ 2 + 6 * x ^ 2 * y = 0 := by
    linarith
  have hcert := oa2x2_polynomialCertificate x y
  have hrhs :
      (2 * y - 2) ^ 2 * (4 * (2 * y) + 3) +
      (3 * x - 2 * y - 1) *
        (4 * (2 * y) * (3 * x - 2 * y + 1) + 8 * (2 * y) ^ 2 + 12) = 0 := by
    nlinarith
  by_contra hle
  have hJ : 1 < 3 * x - 2 * y := lt_of_not_ge hle
  have hs : 0 < 2 * y := by linarith
  have hlinear : 0 < 3 * x - 2 * y + 1 := by linarith
  have hfirst : 0 ≤ (2 * y - 2) ^ 2 * (4 * (2 * y) + 3) := by
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have hinner :
      0 < 4 * (2 * y) * (3 * x - 2 * y + 1) + 8 * (2 * y) ^ 2 + 12 := by
    have hprod : 0 < 4 * (2 * y) * (3 * x - 2 * y + 1) := by positivity
    nlinarith [sq_nonneg (2 * y)]
  have hsecond :
      0 < (3 * x - 2 * y - 1) *
        (4 * (2 * y) * (3 * x - 2 * y + 1) + 8 * (2 * y) ^ 2 + 12) := by
    exact mul_pos (by linarith) hinner
  nlinarith
end OptimalAffinity
