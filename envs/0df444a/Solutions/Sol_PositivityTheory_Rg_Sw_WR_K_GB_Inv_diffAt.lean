-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.Inv.diffAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:54.126164+00:00
-- url     : https://prove2.me/submissions/0725096c-70f6-4b42-b267-d3eb6751932c

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBInvar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open PositivityTheory.Rg.Sw.WR.K.GB.Inv
namespace PositivityTheory.Rg.Sw.WR.K.GB.Inv
theorem _root_.solution {G : Mc n → ℂ} {U : Set (Mc n)} (hU : IsOpen U) (hG : ContDiffOn ℂ (⊤ : ℕ∞) G U)
    {x : Mc n} (hx : x ∈ U) : DifferentiableAt ℂ G x :=
  (hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
end PositivityTheory.Rg.Sw.WR.K.GB.Inv
