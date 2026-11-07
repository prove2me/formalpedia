-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_bases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:20:33.330133+00:00
-- url     : https://prove2.me/submissions/f1d773c0-2020-4512-9c2e-ec113cc05f99

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module
namespace QEC.Coding.HighDimensionalExpander.FiniteGeometry
theorem _root_.solution
    (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V]
    [Finite V] (r : ℕ) (h : Module.finrank k V = r) :
    Nat.card (Basis (Fin r) k V) =
      ∏ i : Fin r, (Fintype.card k ^ r - Fintype.card k ^ i.val) := by
  rw [Nat.card_congr (basesEquivIndependentFrames k V r h)]
  simpa [h, IndependentFrames] using (card_linearIndependent (K := k) (V := V) h.ge)
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
