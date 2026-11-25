-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.sandwich_eU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:20.792471+00:00
-- url     : https://prove2.me/submissions/ebc96547-3000-4122-92e9-eb6c27c8ebef

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_BridgeB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution (Y : Matrix (Fin n) (Fin n) ℂ) (k l a d : Fin n) :
    (Y * Matrix.of (eU k l) * Y) a d = Y a k * Y l d := by
  simp only [Matrix.mul_apply, Matrix.of_apply, eU]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro b _ hb
    rw [Finset.sum_eq_zero]
    · simp
    intro j _
    simp [hb]
  · simp
end PositivityTheory.Rg.Sw.SP
