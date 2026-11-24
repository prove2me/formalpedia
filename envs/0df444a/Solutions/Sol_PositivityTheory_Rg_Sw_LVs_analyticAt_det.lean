-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.analyticAt_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:47.008863+00:00
-- url     : https://prove2.me/submissions/52c37d80-a073-4d60-b92d-39887bb0c4f6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T.det) X := by
  have he : ∀ a b : ι, AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T a b) X := fun a b =>
    ((ContinuousLinearMap.proj b).comp
      (ContinuousLinearMap.proj a : (ι → ι → ℂ) →L[ℂ] (ι → ℂ))).analyticAt X
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i)
end PositivityTheory.Rg.Sw.LVs
