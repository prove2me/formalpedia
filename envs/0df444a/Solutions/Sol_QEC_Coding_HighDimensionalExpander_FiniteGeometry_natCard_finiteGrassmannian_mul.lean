-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.FiniteGeometry.natCard_finiteGrassmannian_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:21:12.086569+00:00
-- url     : https://prove2.me/submissions/cc06133c-c48c-4570-a8be-8676c28660d1

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_FiniteGrassmannian
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_FiniteGeometry_natCard_bases

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.FiniteGeometry
open Module
namespace QEC.Coding.HighDimensionalExpander.FiniteGeometry
theorem _root_.solution
    (k V : Type*) [Field k] [Fintype k] [AddCommGroup V] [Module k V]
    [Finite V] (r : ℕ) (hr : r ≤ Module.finrank k V) :
    Nat.card (FiniteGrassmannian k V r) *
        (∏ i : Fin r, (Fintype.card k ^ r - Fintype.card k ^ i.val)) =
      ∏ i : Fin r,
        (Fintype.card k ^ Module.finrank k V - Fintype.card k ^ i.val) := by
  classical
  letI : Fintype (FiniteGrassmannian k V r) := Fintype.ofFinite _
  have hb (W : FiniteGrassmannian k V r) :
      Nat.card (Basis (Fin r) k W.1) =
        ∏ i : Fin r, (Fintype.card k ^ r - Fintype.card k ^ i.val) :=
    natCard_bases k W.1 r W.property
  calc
    _ = Nat.card (Σ W : FiniteGrassmannian k V r,
        {v : IndependentFrames k V r // frameSpanGrassmannian k V r v = W}) := by
      rw [Nat.card_sigma]
      simp_rw [Nat.card_congr (grassmannianBasisEquivFrameFiber k V r _).symm, hb]
      simp
    _ = Nat.card (IndependentFrames k V r) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv (frameSpanGrassmannian k V r))
    _ = _ := card_linearIndependent hr
end QEC.Coding.HighDimensionalExpander.FiniteGeometry
