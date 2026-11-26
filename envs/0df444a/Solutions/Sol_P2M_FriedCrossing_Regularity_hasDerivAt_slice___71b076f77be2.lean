-- Prove2me | solution 1 for P2M_FriedCrossing_Regularity_hasDerivAt_slice___71b076f77be2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:48:47.294972+00:00
-- url     : https://prove2.me/submissions/77e18d55-f60f-4fdd-a563-2769dbaedf44

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity
namespace FriedCrossing.Regularity
theorem _root_.solution {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2)
    (θ τ : ℝ) :
    HasDerivAt (fun s => f s τ) (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) (θ, τ) (1, 0)) θ := by
  have h1 := (hf (θ, τ)).hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => ((s, τ) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_id θ).prodMk (hasDerivAt_const θ τ)
  exact HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => ((s, τ) : ℝ × ℝ)) θ h1 h2
end FriedCrossing.Regularity
