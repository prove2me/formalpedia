-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.dph_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:40:50.974399+00:00
-- url     : https://prove2.me/submissions/e681c831-6919-4ba9-9027-5e679c920772

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
theorem _root_.solution (a : Fin n) : (dph a)ᴴ * dph a = 1 := by
  rw [dph, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i
  by_cases hi : i = a <;> simp [hi]
end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
