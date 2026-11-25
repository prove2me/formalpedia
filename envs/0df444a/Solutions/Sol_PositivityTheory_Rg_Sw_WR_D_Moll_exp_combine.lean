-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.Moll.exp_combine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:49.614876+00:00
-- url     : https://prove2.me/submissions/41fc8982-2cde-4318-a661-bfa05f1edb51

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_MollId
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ExpCombine
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_ip_comm
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_Moll_ip_sub_right


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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D PositivityTheory.Rg.Sw.WR.D.Moll
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
namespace PositivityTheory.Rg.Sw.WR.D.Moll
theorem _root_.solution (t : ℝ) (y q β : E n) :
    Complex.exp (Complex.I * t * ip y q) * Complex.exp (-(Complex.I * t * ip β y)) =
      Complex.exp (Complex.I * t * ip y (q - β)) := by
  rw [ip_sub_right, ip_comm β y, ← Complex.exp_add]
  congr 1
  push_cast
  ring
end PositivityTheory.Rg.Sw.WR.D.Moll
