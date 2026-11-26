-- Prove2me | solution 1 for P2M_FriedCrossing_Regularity_hasDerivAt_p__ad8317175eea
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:51:41.783488+00:00
-- url     : https://prove2.me/submissions/1be8db19-8463-40a5-956c-99f5e4c02855

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Regularity_hasDerivAt_slice___8fe3429faa04
import Theorems.Thm_P2M_FriedCrossing_Regularity_p__eq_f2d456397895

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity
namespace FriedCrossing.Regularity
theorem _root_.solution {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2)
    (θ τ : ℝ) : HasDerivAt (fun t => f θ t) (pτ f θ τ) τ := by
  rw [pτ_eq hf]; exact hasDerivAt_slice_τ hf θ τ
end FriedCrossing.Regularity
