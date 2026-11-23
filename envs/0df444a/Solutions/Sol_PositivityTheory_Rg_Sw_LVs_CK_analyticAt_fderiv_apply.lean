-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.analyticAt_fderiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:25.629125+00:00
-- url     : https://prove2.me/submissions/8c86cd1a-1d5e-4cd3-a1a8-c834c3312f13

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerCornerInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDeterminantPowerZeroInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.LVs.CK
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {N : ℕ}
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (G : F → ℂ) (x v : F) (hG : AnalyticAt ℂ G x) : AnalyticAt ℂ (fun y => fderiv ℂ G y v) x := by
  have h2 : AnalyticAt ℂ (fun L : F →L[ℂ] ℂ => L v) (fderiv ℂ G x) :=
    (ContinuousLinearMap.apply ℂ ℂ v).analyticAt _
  exact h2.comp hG.fderiv
end PositivityTheory.Rg.Sw.LVs.CK
