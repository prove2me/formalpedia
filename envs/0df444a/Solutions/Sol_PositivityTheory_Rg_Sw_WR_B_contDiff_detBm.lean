-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.contDiff_detBm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:00.533831+00:00
-- url     : https://prove2.me/submissions/2b857044-1ab7-495e-b92c-759edfd5ca86

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_Bm_entry
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_det_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution (s : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => (Bm s y).det) :=
  contDiff_det_of (contDiff_Bm_entry s)
end PositivityTheory.Rg.Sw.WR.B
