-- Prove2me | solution 1 for OptimalAffinity.oa2x2_current_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:59:59.337605+00:00
-- url     : https://prove2.me/submissions/c6ae3c62-5ee4-422d-9e2d-9952c6a0bfa7

module
public import Definitions.Def_proofs_OptimalAffinity_Steady
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Theorems.Thm_OptimalAffinity_oa2x2_polynomialCertificate
public import Theorems.Thm_OptimalAffinity_oa2x2_current_formula
public import Theorems.Thm_OptimalAffinity_oa2x2_one_one_current
public import Theorems.Thm_OptimalAffinity_oa2x2_ySteady_iff


set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution
    (x y : ℝ) (hy : 0 < y) (hsteady : YSteady oa2x2 x y) :
    productionCurrent oa2x2 x y = 1 ↔ x = 1 ∧ y = 1 := by
  constructor
  · intro hJ
    rw [oa2x2_current_formula] at hJ
    have hsteady' := (oa2x2_ySteady_iff x y).mp hsteady
    have hzero : 3 * x - 2 * y - 7 * y ^ 2 + 6 * x ^ 2 * y = 0 := by
      linarith
    have hcert := oa2x2_polynomialCertificate x y
    have hJzero : 3 * x - 2 * y - 1 = 0 := by linarith
    have hfirstzero : (2 * y - 2) ^ 2 * (4 * (2 * y) + 3) = 0 := by
      rw [hzero, hJzero] at hcert
      norm_num only [mul_zero, zero_mul, add_zero] at hcert
      exact hcert.symm
    have hfactor : 4 * (2 * y) + 3 ≠ 0 := ne_of_gt (by linarith)
    have hsquare : (2 * y - 2) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hfirstzero with hsquare | hbad
      · exact hsquare
      · exact (hfactor hbad).elim
    have hy1 : y = 1 := by nlinarith [sq_nonneg (2 * y - 2)]
    constructor
    · nlinarith
    · exact hy1
  · rintro ⟨rfl, rfl⟩
    exact oa2x2_one_one_current
end OptimalAffinity
