-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.word_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:52:55.174035+00:00
-- url     : https://prove2.me/submissions/839214ac-8002-4b17-80ab-379420d02211

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBLink

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.K PositivityTheory.Rg.Sw.WR.K.GB
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
variable {F G : Mc n → ℂ} {U : Set (Mc n)}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (L₁ L₂ : List (Fin n × Fin n)) (H : Mc n → ℂ) :
    word (L₁ ++ L₂) H = word L₁ (word L₂ H) := by
  simp [word, List.foldr_append]
end PositivityTheory.Rg.Sw.WR.K.GB
