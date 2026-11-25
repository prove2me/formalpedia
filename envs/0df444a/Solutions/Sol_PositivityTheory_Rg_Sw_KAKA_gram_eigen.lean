-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.KAKA.gram_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:44:32.117871+00:00
-- url     : https://prove2.me/submissions/ef965c59-ccce-443f-9fe8-2793826d8c2c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AbsoluteConvergence_GramDiagUnitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.KAKA
open Matrix
namespace PositivityTheory.Rg.Sw.KAKA
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ (W : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℝ), Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      (A * W)ᴴ * (A * W) = diagonal (fun j => (l j : ℂ)) := by
  have hG : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  have hdiag := hG.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at hdiag
  refine ⟨(hG.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), hG.eigenvalues, ?_, ?_, ?_⟩
  · have := Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2
    simpa [Matrix.star_eq_conjTranspose] using this
  · have := Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2
    simpa [Matrix.star_eq_conjTranspose] using this
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
      hdiag]
    rfl
end PositivityTheory.Rg.Sw.KAKA
