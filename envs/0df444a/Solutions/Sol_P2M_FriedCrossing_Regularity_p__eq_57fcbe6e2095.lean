-- Prove2me | solution 1 for P2M_FriedCrossing_Regularity_p__eq_57fcbe6e2095
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:50:49.391352+00:00
-- url     : https://prove2.me/submissions/200495aa-6ae0-4eeb-9e4c-947922db06ff

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Regularity_hasDerivAt_slice___71b076f77be2

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity
namespace FriedCrossing.Regularity
theorem _root_.solution {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2) (θ τ : ℝ) :
    pθ f θ τ = fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) (θ, τ) (1, 0) :=
  (hasDerivAt_slice_θ hf θ τ).deriv
end FriedCrossing.Regularity
