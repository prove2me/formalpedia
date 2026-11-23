-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.differentiableAt_of_cdo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:36.008077+00:00
-- url     : https://prove2.me/submissions/723eac32-9400-4a52-8270-8a2f70208af5

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
theorem _root_.solution (hU : IsOpen U) (hF : ContDiffOn ℂ (⊤ : ℕ∞) F U) {b : Mc n} (hb : b ∈ U) :
    DifferentiableAt ℂ F b :=
  ((hF.contDiffAt (hU.mem_nhds hb)).differentiableAt (by norm_cast))
end PositivityTheory.Rg.Sw.WR.K.GB
