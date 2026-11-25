-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.mX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:49:35.202494+00:00
-- url     : https://prove2.me/submissions/ac527328-06f8-4dc0-9033-767e18482029

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeH
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Z_ext


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
theorem _root_.solution (s : ℂ) (x v : MC n) (t : ℂ) :
    1 - (Complex.I * s) • Matrix.of (x + t • v) = (1 - (Complex.I * s) • Matrix.of x) + t • (-(Complex.I * s) • Matrix.of v) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring
end PositivityTheory.Rg.Sw.SP
