-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.posDef_det_re_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:01:44.100663+00:00
-- url     : https://prove2.me/submissions/a27899aa-19fd-4d19-815c-34caf100da2f

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    0 < G.det.re ∧ G.det.im = 0 := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hG.det_pos
  exact ⟨h1, h2.symm⟩
end ReciprocityTheory.GeometryOfNumbersTheory
