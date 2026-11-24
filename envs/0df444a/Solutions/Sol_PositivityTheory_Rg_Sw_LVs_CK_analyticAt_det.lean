-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.analyticAt_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:26:36.200796+00:00
-- url     : https://prove2.me/submissions/e89ca538-0808-4ff3-aa8b-56f78cfbf954

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_CayleyA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDet

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
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw.LVs
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (M0 : Matrix ι ι ℂ) :
    AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T.det) M0 := by
  have he : ∀ a b : ι, AnalyticAt ℂ (fun T : Matrix ι ι ℂ => T a b) M0 := fun a b =>
    ((ContinuousLinearMap.proj b).comp
      (ContinuousLinearMap.proj a : (ι → ι → ℂ) →L[ℂ] (ι → ℂ))).analyticAt M0
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ fun i _ => he (σ i) i)
end PositivityTheory.Rg.Sw.LVs.CK
