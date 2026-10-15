-- Prove2me | solution 1 for ThreeSum.IndexedGreedy.argmax_range
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:41:36.390689+00:00
-- url     : https://prove2.me/submissions/f81dac34-2e78-4b86-8562-0cfe7e1cffbd

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum

section


/-!
# Linking array extrema to the finite greedy-cover definition

The program scans indices in increasing order and retains the first
maximum. This is exactly the tie rule in `List.argmax` used by the
mathematical cover construction.
-/

namespace ThreeSum.IndexedGreedy

open LightMinimum

theorem argmax_range_sourceProof (f : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    (List.range n).argmax f = some (least (fun i => -(f i : ℤ)) n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [least]
    | succ n =>
      rw [List.range_succ,List.argmax_concat,ih (by omega)]
      change (if f (least (fun i => -(f i : ℤ)) (n+1)) < f (n+1)
        then some (n+1) else some (least (fun i => -(f i : ℤ)) (n+1))) =
        some (if -(f (n+1) : ℤ) < -(f (least (fun i => -(f i : ℤ)) (n+1)) : ℤ)
          then n+1 else least (fun i => -(f i : ℤ)) (n+1))
      split_ifs <;> first | rfl | omega
































end ThreeSum.IndexedGreedy

end


theorem solution : ∀ (f : Nat → Nat) {n : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @Eq.{1} (Option.{0} Nat) (@List.argmax.{0, 0} Nat Nat Nat.instPreorder Nat.decLt f (List.range n))
      (@Option.some.{0} Nat
        (ThreeSum.LightMinimum.least
          (fun (i : Nat) => @Neg.neg.{0} Int Int.instNegInt (@Nat.cast.{0} Int instNatCastInt (f i))) n)) := by
  exact @ThreeSum.IndexedGreedy.argmax_range_sourceProof

#print axioms solution
