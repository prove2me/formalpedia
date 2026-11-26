-- Prove2me | solution 1 for P2M_FriedCrossing_Regularity_hasDerivAt_slice___8fe3429faa04
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:48:35.872985+00:00
-- url     : https://prove2.me/submissions/2b3d2d75-e579-4538-aa81-bb89cc1b43ca

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
    HasDerivAt (fun t => f θ t) (fderiv ℝ (fun q : ℝ × ℝ => f q.1 q.2) (θ, τ) (0, 1)) τ := by
  have h1 := (hf (θ, τ)).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ((θ, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) τ :=
    (hasDerivAt_const τ θ).prodMk (hasDerivAt_id τ)
  exact HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => ((θ, t) : ℝ × ℝ)) τ h1 h2
end FriedCrossing.Regularity
