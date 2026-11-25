-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.K.GB.pb_cd_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:13.375811+00:00
-- url     : https://prove2.me/submissions/b2968b07-0ef4-47fd-8780-1963a0ef5d6a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ClsGainBSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_GBBound

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.K.GB
theorem _root_.solution (i j : Fin n) : ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => b i j) :=
  contDiff_apply_apply (𝕜 := ℂ) (E := ℂ) i j
end PositivityTheory.Rg.Sw.WR.K.GB
