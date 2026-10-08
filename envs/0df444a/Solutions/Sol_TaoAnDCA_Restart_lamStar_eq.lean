-- Prove2me | solution 1 for TaoAnDCA.Restart.lamStar_eq
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:30:47.085164+00:00
-- url     : https://prove2.me/submissions/42199795-e9e8-403e-9a13-d73282286f00

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting
open TaoAnDCA.Restart

theorem solution {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (xs : EuclideanSpace ℝ (Fin n)) (lamStar : ℝ) (hkkt : TaoAnDCA.TRS.IsKKT A b r xs lamStar) :
    lamStar = (-(inner ℝ xs (A xs)) - inner ℝ xs b) / r ^ 2 := by


  obtain ⟨hl, he, hcomp, hnorm⟩ := hkkt
  have hi := congrArg (fun z => inner ℝ xs z) he
  simp only [inner_add_right, inner_smul_right, inner_neg_right,
    real_inner_self_eq_norm_sq] at hi
  apply (eq_div_iff (pow_ne_zero 2 hr.ne')).mpr
  rcases mul_eq_zero.mp hcomp with hz | hz
  · simp only [hz, zero_mul, zero_add] at hi ⊢
    linarith
  · have hn : ‖xs‖ = r := sub_eq_zero.mp hz
    rw [hn] at hi
    linarith
#print axioms solution

