-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.continuous_Fi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:13.270228+00:00
-- url     : https://prove2.me/submissions/bb3694ef-dbab-4541-aec2-d2e9eb589b3d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_evXD
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_gsD
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_ip_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {m n : ℕ}
variable (ε : Fin m → Bool) (c t : ℝ)
variable {ε c t}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (hq : Continuous (qX (n := n) ε)) (P : PX m n) (y : E n) : Continuous (Fi ε c t P y) := by
  unfold Fi
  refine ((continuous_evXD P).mul (continuous_gsD c)).mul (Complex.continuous_exp.comp ?_)
  exact continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_ip_right y).comp hq))
end PositivityTheory.Rg.Sw.WR.D
