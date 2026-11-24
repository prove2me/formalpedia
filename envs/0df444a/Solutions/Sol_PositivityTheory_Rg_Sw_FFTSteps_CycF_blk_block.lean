-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.FFTSteps.CycF.blk_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:14:04.569368+00:00
-- url     : https://prove2.me/submissions/cd205b20-c09a-49ea-8765-073b3131370e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_CycFFTA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.FFTSteps PositivityTheory.Rg.Sw.FFTSteps.CycF
variable {m n : ℕ} (ε : Fin m → Bool)
variable {ε}
namespace PositivityTheory.Rg.Sw.FFTSteps.CycF
theorem _root_.solution (β : Bool) (v : Matrix (Rw ε β) (Rw ε β) ℂ) (a b : Fin m) (h : ε a ≠ ε b) : blk ε β v a b = 0 := by
  unfold blk
  by_cases ha : ε a = β
  · rw [dif_pos ha, dif_neg (fun hb => h (ha.trans hb.symm))]
  · rw [dif_neg ha, if_neg (fun e : a = b => h (congrArg ε e))]
end PositivityTheory.Rg.Sw.FFTSteps.CycF
