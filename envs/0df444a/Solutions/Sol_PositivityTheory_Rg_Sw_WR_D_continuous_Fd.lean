-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.continuous_Fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:21:24.620941+00:00
-- url     : https://prove2.me/submissions/2fc942bc-c738-4c11-a953-79991c6d0dcb

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_Lc_comp
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_Fi

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
theorem _root_.solution (hq : Continuous (qX (n := n) ε)) (P : PX m n) (y : E n) : Continuous (Fd ε c t P y) := by
  unfold Fd
  have h1 : Continuous fun x => evX P x * gs c x * Complex.exp (Complex.I * t * ip y (qX ε x)) * (Complex.I * t) :=
    (continuous_Fi hq P y).mul continuous_const
  exact h1.smul (continuous_Lc_comp hq)
end PositivityTheory.Rg.Sw.WR.D
