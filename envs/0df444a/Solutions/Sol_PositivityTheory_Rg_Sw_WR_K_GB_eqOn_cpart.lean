-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.eqOn_cpart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:36.303286+00:00
-- url     : https://prove2.me/submissions/3ef8b4cf-90c4-46f2-98e3-8861deb12a50

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {F G : Mc n → ℂ} {U : Set (Mc n)}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (i j : Fin n) (hU : IsOpen U) {H H' : Mc n → ℂ} (h : Set.EqOn H H' U) :
    Set.EqOn (cpart i j H) (cpart i j H') U := fun b hb => by
  have : H =ᶠ[nhds b] H' := Filter.eventuallyEq_of_mem (hU.mem_nhds hb) h
  simp only [cpart, this.fderiv_eq]
end PositivityTheory.Rg.Sw.WR.K.GB
