-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.TW.TD_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:54.775321+00:00
-- url     : https://prove2.me/submissions/780821e2-2b0b-4a85-aa89-a64002fd7f8a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_Lagr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBTwist
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_contDiff_Dkl
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_contDiff_om
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_K_GB_TW_contDiff_sh

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
theorem _root_.solution {c : ℕ → E n → ℂ} (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j)) (k l : Fin n) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (TD k l c j) :=
  (contDiff_Dkl (hc j) k l).sub ((contDiff_om k l).mul (contDiff_sh hc j))
end PositivityTheory.Rg.Sw.WR.K.GB.TW
