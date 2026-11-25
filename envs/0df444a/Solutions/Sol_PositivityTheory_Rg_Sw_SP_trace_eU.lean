-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.trace_eU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:40.550518+00:00
-- url     : https://prove2.me/submissions/cc109e67-112f-4b26-874c-3d0d85fd5c63

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
theorem _root_.solution (Y : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) : (Y * Matrix.of (eU k l)).trace = Y l k := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, eU]
  rw [Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro b _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hb]
  · simp
end PositivityTheory.Rg.Sw.SP
