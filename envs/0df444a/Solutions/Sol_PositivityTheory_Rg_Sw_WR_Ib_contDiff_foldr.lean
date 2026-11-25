-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.Ib.contDiff_foldr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:19.212835+00:00
-- url     : https://prove2.me/submissions/fc3892fd-ebb3-4829-871d-5af65fcd8f32

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_IntegrableOfBound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_Ib_contDiff_dkl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Ib
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.Ib
theorem _root_.solution {f : E n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : List (Fin n × Fin n)) :
    ContDiff ℝ (⊤ : ℕ∞) (L.foldr (fun kl g => Dkl kl.1 kl.2 g) f) := by
  induction L with
  | nil => simpa using hf
  | cons kl L ih => simpa using contDiff_dkl ih kl.1 kl.2
end PositivityTheory.Rg.Sw.WR.Ib
