-- Prove2me | solution 1 for P2M_FriedCrossing_Regularity_contDiff_p__a098e3e32f33
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:52:18.238231+00:00
-- url     : https://prove2.me/submissions/c1eda350-7a29-4523-929e-7ed13beef791

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Regularity_p__eq_57fcbe6e2095
import Theorems.Thm_FriedCrossing_Regularity_differentiable_of_contDiff

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity
namespace FriedCrossing.Regularity
theorem _root_.solution {f : ℝ → ℝ → ℝ} {m n : WithTop ℕ∞} (hmn : m + 1 ≤ n)
    (hf : ContDiff ℝ n fun q : ℝ × ℝ => f q.1 q.2) :
    ContDiff ℝ m fun q : ℝ × ℝ => pθ f q.1 q.2 := by
  have hd := differentiable_of_contDiff hmn hf
  have : (fun q : ℝ × ℝ => pθ f q.1 q.2) =
      fun q : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) q (1, 0) := by
    funext q; exact pθ_eq hd q.1 q.2
  rw [this]
  exact (hf.fderiv_right hmn).clm_apply contDiff_const
end FriedCrossing.Regularity
