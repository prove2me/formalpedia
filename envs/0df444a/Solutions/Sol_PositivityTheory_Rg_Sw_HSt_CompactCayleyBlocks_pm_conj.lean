-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.pm_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:40:54.332696+00:00
-- url     : https://prove2.me/submissions/bea7e5ac-11bd-42b6-85e9-cdcb0fb9c0c9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_SpanUnitaryMatrix

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (X : Matrix (Fin n) (Fin n) ℂ) :
    pm σ * X * (pm σ)ᴴ = X.submatrix σ σ := by
  ext i j
  simp [pm, Matrix.mul_apply, Matrix.conjTranspose_apply, eq_comm]
end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
