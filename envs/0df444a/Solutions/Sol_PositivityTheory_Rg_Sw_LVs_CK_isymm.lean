-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.CK.isymm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:15:26.033035+00:00
-- url     : https://prove2.me/submissions/62cb11e1-3405-4eed-858f-30dd0d342807

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_AnalyticAtDet
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DetDFin

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
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace PositivityTheory.Rg.Sw.LVs.CK
theorem _root_.solution (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin n → F) (π : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℂ n G x (u ∘ π) = iteratedFDeriv ℂ n G x u :=
  hG.contDiffAt.iteratedFDeriv_comp_perm u π
end PositivityTheory.Rg.Sw.LVs.CK
