-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.iteratedDeriv_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:15.363905+00:00
-- url     : https://prove2.me/submissions/8a561fc6-7d19-4c01-9d28-442f2a2c3c08

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution {N : ℕ} (K : EuclideanSpace ℝ ι → ℂ) (hK : ContDiff ℝ N K) (ξ : EuclideanSpace ℝ ι)
    {k : ℕ} (hk : k ≤ N) :
    iteratedDeriv k (fun t : ℝ => K (t • ξ)) 0 = iteratedFDeriv ℝ k K 0 (fun _ => ξ) := by
  have e : (fun t : ℝ => K (t • ξ)) = K ∘ (ContinuousLinearMap.toSpanSingleton ℝ ξ) := by
    funext t; simp [ContinuousLinearMap.toSpanSingleton_apply]
  rw [e, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right _ hK _ (by exact_mod_cast hk)]
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearMap.toSpanSingleton_apply]
end PositivityTheory.SiegelWeilFormula.KFPB
