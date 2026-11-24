-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.analyticAt_piF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:41.740909+00:00
-- url     : https://prove2.me/submissions/e443d624-b229-4905-a051-77f4ad4f4237

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
theorem _root_.solution (X0 : Matrix (Fin N) (Fin (N + 1)) ℂ) :
    AnalyticAt ℂ (piF : Matrix (Fin N) (Fin (N + 1)) ℂ → Matrix (Fin N) (Fin N) ℂ) X0 :=
  (piL N).analyticAt X0
end PositivityTheory.Rg.Sw.LVs.CK
