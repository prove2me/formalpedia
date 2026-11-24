-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.analyticAt_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:46.188062+00:00
-- url     : https://prove2.me/submissions/f1c788c3-0104-44c6-8255-a2e685fed1d9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDeterminantPowerZeroInt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_FderivDeterminantPowerColumnSum

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
theorem _root_.solution (k : Fin N) (j : Fin (N + 1)) (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) :
    AnalyticAt ℂ (fun X : Matrix (Fin N) (Fin (N + 1)) ℂ => X k j) X0 := by
  have := (LinearMap.toContinuousLinearMap
    (Matrix.entryLinearMap ℂ ℂ k j : Matrix (Fin N) (Fin (N + 1)) ℂ →ₗ[ℂ] ℂ)).analyticAt X0
  exact this
end PositivityTheory.Rg.Sw.LVs.CK
