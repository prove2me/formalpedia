-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.det_affine_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:36.460476+00:00
-- url     : https://prove2.me/submissions/f3d9ba9c-1578-44cf-9388-4dbc48aba886

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (M0 A : Matrix (Fin n) (Fin n) ℂ) (h : M0.det ≠ 0) :
    ∀ᶠ t : ℂ in 𝓝 0, (M0 + t • A).det ≠ 0 := by
  have hc : Continuous fun t : ℂ => (M0 + t • A).det :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have : (fun t : ℂ => (M0 + t • A).det) 0 ≠ 0 := by simpa using h
  exact hc.continuousAt.eventually_ne this
end PositivityTheory.Rg.Sw.SP
