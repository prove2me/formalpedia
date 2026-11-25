-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.contDiff_herm_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:32.525445+00:00
-- url     : https://prove2.me/submissions/1ae5a146-2191-474f-aa90-3b109db5417f

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_contDiff_coord

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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
open PositivityTheory.Rg.Sw.WR.K.GB.TW
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB.TW
theorem _root_.solution (i j : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => herm y i j) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((y i j + y j i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_coord i j).add (contDiff_coord j i))
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => ((y i j - y j i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_coord i j).sub (contDiff_coord j i))
  simp only [herm]
  exact (h1.div_const 2).add ((contDiff_const.mul h2).div_const 2)
end PositivityTheory.Rg.Sw.WR.K.GB.TW
