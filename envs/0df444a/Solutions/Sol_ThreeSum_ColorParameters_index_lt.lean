-- Prove2me | solution 1 for ThreeSum.ColorParameters.index_lt
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:42:32.613429+00:00
-- url     : https://prove2.me/submissions/e15732d1-92af-4b4d-a5cc-7c6f52f48129

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# A literal small coloring-parameter order

There are exactly 81*W² integer slots. Four ternary digits select the
color map, and the remaining quotient selects its two binary coordinates.
The inverse code proves that every separating parameter is present.
-/

namespace ThreeSum.ColorParameters







































theorem coordinate_pair_lt {W : ℕ} (p : Coloring.Parameter W) :
    p.1.1.val*W+p.1.2.val < W*W := by
  calc
    _ < p.1.1.val*W+W := Nat.add_lt_add_left p.1.2.isLt _
    _ = (p.1.1.val+1)*W := by ring
    _ ≤ W*W := Nat.mul_le_mul_right _ (by omega)

theorem index_lt_sourceProof {W : ℕ} (p : Coloring.Parameter W) : index p < count W := by
  have hp := coordinate_pair_lt p
  have h0 := (p.2 (false,false)).isLt
  have h1 := (p.2 (false,true)).isLt
  have h2 := (p.2 (true,false)).isLt
  have h3 := (p.2 (true,true)).isLt
  unfold index count
  rw [pow_two]
  omega




































end ThreeSum.ColorParameters

end


theorem solution : ∀ {W : Nat} (p : ThreeSum.Coloring.Parameter W),
  @LT.lt.{0} Nat instLTNat (@ThreeSum.ColorParameters.index W p) (ThreeSum.ColorParameters.count W) := by
  exact @ThreeSum.ColorParameters.index_lt_sourceProof

#print axioms solution
