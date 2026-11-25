-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks.dph_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:42:02.014644+00:00
-- url     : https://prove2.me/submissions/c569bfe5-5852-41ee-b148-809d46facb3b

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
theorem _root_.solution {a b : Fin n} (hab : a ≠ b) :
    dph a * Matrix.single a b (1 : ℂ) * (dph a)ᴴ = Complex.I • Matrix.single a b (1 : ℂ) := by
  ext i j
  rw [dph, diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.single_apply, Matrix.smul_apply, smul_eq_mul, Pi.star_apply]
  by_cases hi : a = i <;> by_cases hj : b = j
  · subst hi hj; simp [hab.symm]
  · simp [hj]
  · simp [hi]
  · simp [hi, hj]
end PositivityTheory.Rg.Sw.HSt.CompactCayleyBlocks
