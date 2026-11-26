-- Prove2me | solution 1 for P2M_FriedCrossing_Regularity_p__eq_f2d456397895
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:49:33.707066+00:00
-- url     : https://prove2.me/submissions/81e89d3c-5c8d-45ed-bbe5-003a2f9f8738

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Regularity_hasDerivAt_slice___8fe3429faa04

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity
namespace FriedCrossing.Regularity
theorem _root_.solution {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2) (θ τ : ℝ) :
    pτ f θ τ = fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) (θ, τ) (0, 1) :=
  (hasDerivAt_slice_τ hf θ τ).deriv
end FriedCrossing.Regularity
