-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.valuation_det_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:17.21668+00:00
-- url     : https://prove2.me/submissions/d0e7e0b7-1c9e-41a0-b20a-4aa146fcb6c8

import Definitions.Def_ReciprocityTheory_DualLattices_TensorSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {X : Type} [Fintype X] [DecidableEq X]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (v : Valuation C NNReal) (hv : v.Integers R) (P : Matrix X X C)
    (hP : ∀ x j, ∃ r : R, algebraMap R C r = P x j) : v P.det ≤ 1 := by
  choose r hr using hP
  have : P = (Matrix.of r).map (algebraMap R C) := by ext x j; simp [hr]
  rw [this, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact hv.map_le_one _
end ReciprocityTheory.PGsh.L2
