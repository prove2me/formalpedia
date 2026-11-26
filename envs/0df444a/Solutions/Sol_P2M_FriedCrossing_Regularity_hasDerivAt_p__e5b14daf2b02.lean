-- Prove2me | solution 1 for P2M_FriedCrossing_Regularity_hasDerivAt_p__e5b14daf2b02
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:52:16.393208+00:00
-- url     : https://prove2.me/submissions/12a74811-cbb3-4886-8658-649dd4ad2012

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Regularity_hasDerivAt_slice___71b076f77be2
import Theorems.Thm_P2M_FriedCrossing_Regularity_p__eq_57fcbe6e2095

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Regularity
namespace FriedCrossing.Regularity
theorem _root_.solution {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ fun q : ℝ × ℝ => f q.1 q.2)
    (θ τ : ℝ) : HasDerivAt (fun s => f s τ) (pθ f θ τ) θ := by
  rw [pθ_eq hf]; exact hasDerivAt_slice_θ hf θ τ
end FriedCrossing.Regularity
