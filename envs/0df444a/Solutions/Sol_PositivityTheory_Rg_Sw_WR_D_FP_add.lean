-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.FP_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:16:19.747923+00:00
-- url     : https://prove2.me/submissions/3ed225ae-d7d3-4e63-bc2e-1b29a643bb91

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivFA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DerivF
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_FP_eq_integral_Fi
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_integrable_Fi


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
variable {m n : ℕ} {ε : Fin m → Bool} {c t : ℝ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (hI : IntG) (hA : AlgA) (hc : 0 < c) (P Q : PX m n) :
    FP ε c t (P + Q) = FP ε c t P + FP ε c t Q := by
  have hq := (hA m n ε).2.2.2.2
  funext y
  simp only [Pi.add_apply]
  rw [FP_eq_integral_Fi, FP_eq_integral_Fi, FP_eq_integral_Fi,
    ← integral_add (integrable_Fi hI hq hc P y) (integrable_Fi hI hq hc Q y)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [Fi, evX, map_add]; ring
end PositivityTheory.Rg.Sw.WR.D
