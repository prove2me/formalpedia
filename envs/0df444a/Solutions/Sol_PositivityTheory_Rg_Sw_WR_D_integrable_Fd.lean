-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.integrable_Fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:27:29.387057+00:00
-- url     : https://prove2.me/submissions/abb5ac93-cc99-441e-b427-b017a75eefe1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_Fd
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_integrable_bnd
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_norm_Fd_le

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
theorem _root_.solution (hI : IntG) (hq : Continuous (qX (n := n) ε)) (hc : 0 < c) (P : PX m n) (y : E n) :
    Integrable (Fd ε c t P y) :=
  (integrable_bnd hI hc P).mono' (continuous_Fd hq P y).aestronglyMeasurable (ae_of_all _ fun x => norm_Fd_le P y x)
end PositivityTheory.Rg.Sw.WR.D
