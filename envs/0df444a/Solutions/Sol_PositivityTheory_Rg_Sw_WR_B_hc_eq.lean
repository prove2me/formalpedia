-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.B.hc_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:22.331452+00:00
-- url     : https://prove2.me/submissions/f1a2e25a-11ba-4f61-a143-f9435bd7ae7d

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsBoundB

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.B
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.B
theorem _root_.solution (w : Fin n → Fin n → ℂ) :
    herm (fun a b => (w a b).re) + Complex.I • herm (fun a b => (w a b).im) =
      fun i j => (1 + Complex.I) / 2 * w i j + (1 - Complex.I) / 2 * w j i := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, herm, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring
end PositivityTheory.Rg.Sw.WR.B
