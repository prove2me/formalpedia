-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.herm_hinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:59:05.502961+00:00
-- url     : https://prove2.me/submissions/7e6e9258-0c10-44bc-9733-04ccb701cd0e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvX

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, star (T i j) = T j i) : herm (hinv T) = T := by
  ext i j
  have h1 : (T j i).re = (T i j).re := by rw [← hT i j]; simp
  have h2 : (T j i).im = -(T i j).im := by rw [← hT i j]; simp
  apply Complex.ext
  · simp [herm, hinv, h1, h2]
    try ring
  · simp [herm, hinv, h1, h2]
    try ring
end PositivityTheory.Rg.Sw.WR.D
