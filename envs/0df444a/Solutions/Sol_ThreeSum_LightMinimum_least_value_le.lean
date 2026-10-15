-- Prove2me | solution 1 for ThreeSum.LightMinimum.least_value_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:37:44.737947+00:00
-- url     : https://prove2.me/submissions/615fa595-b0da-4ee5-ac39-f339a3ba93c3

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light

section


/-!
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum

open Light






















theorem least_value_le_sourceProof (f : ℕ → ℤ) (n i : ℕ) (hi : i < n) :
    f (least f n) ≤ f i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases h : f n < f (least f n)
      · rw [least, if_pos h]
        by_cases hin : i < n
        · exact h.le.trans (ih hin)
        · have he : i = n := by omega
          simp [he]
      · rw [least, if_neg h]
        by_cases hin : i < n
        · exact ih hin
        · have he : i = n := by omega
          simpa only [he] using le_of_not_gt h











variable {lim : Limits} {P : Program} {d : ℕ}





































end ThreeSum.LightMinimum

end


theorem solution : ∀ (f : Nat → Int) (n i : Nat),
  @LT.lt.{0} Nat instLTNat i n → @LE.le.{0} Int Int.instLEInt (f (ThreeSum.LightMinimum.least f n)) (f i) := by
  exact @ThreeSum.LightMinimum.least_value_le_sourceProof

#print axioms solution
