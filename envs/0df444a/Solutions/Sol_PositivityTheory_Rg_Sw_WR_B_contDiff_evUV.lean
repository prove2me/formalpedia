-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.contDiff_evUV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:58:58.304987+00:00
-- url     : https://prove2.me/submissions/3e53923d-c205-4e6d-afb0-7344ed8fd764

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_ent
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_B_contDiff_eval


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
theorem _root_.solution {s : ℂ} (hs : s = 1 ∨ s = -1) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (evUV s R) :=
  contDiff_eval (fun e y => ent s e y) (contDiff_ent hs) R
end PositivityTheory.Rg.Sw.WR.B
