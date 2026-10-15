-- Prove2me | solution 1 for ThreeSum.OutputDecodeOrder.tuples_getD_indices
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:00:25.022089+00:00
-- url     : https://prove2.me/submissions/859eb444-cc46-4e25-97ec-db857a179f4e

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists

section


/-!
# Exact physical tuple indices for output decoding

The product enumerator is lexicographic: its first block is the outermost
choice. Repeated integer key values have no role in these index equations.
The recursive decoder takes the final coordinate by division and remainder.
-/

namespace ThreeSum.OutputDecodeOrder

open RadixKeyLists

set_option maxHeartbeats 1800000
set_option maxRecDepth 6000

variable {α β : Type*}
























theorem tuples_succ_right (base : List α) (J : ℕ) :
    tuples base (J+1) = (tuples base J).flatMap fun xs => base.map fun a => xs++[a] := by
  induction J with
  | zero =>
    have hh : base.flatMap (fun a => [[a]]) = base.map (fun a => [a]) := by
      induction base with
      | nil => rfl
      | cons a xs ih => simp [ih]
    simpa [tuples] using hh
  | succ J ih =>
    calc
      _ = base.flatMap (fun a => (tuples base (J+1)).map (List.cons a)) := rfl
      _ = base.flatMap (fun a => ((tuples base J).flatMap
          (fun xs => base.map (fun b => xs++[b]))).map (List.cons a)) := by rw [ih]
      _ = (base.flatMap (fun a => (tuples base J).map (List.cons a))).flatMap
          (fun xs => base.map (fun a => xs++[a])) := by
        simp only [List.map_flatMap,List.flatMap_assoc,List.flatMap_map,List.map_map,Function.comp_def,
          List.cons_append]
      _ = _ := rfl













































theorem tuples_getD_indices_sourceProof (base : List α) (da : α) (hm : 0 < base.length)
    (J k : ℕ) (hk : k < base.length^J) :
    (tuples base J).getD k [] = (indices base.length J k).map (fun i => base.getD i da) := by
  induction J generalizing k with
  | zero =>
    have hk0 : k=0 := by simpa using hk
    subst k
    rfl
  | succ J ih =>
    have hq : k/base.length < base.length^J :=
      (Nat.div_lt_iff_lt_mul hm).mpr (by simpa only [pow_succ] using hk)
    have hr : k%base.length < base.length := Nat.mod_lt _ hm
    have hi : k/base.length < (tuples base J).length := by rwa [tuples_length]
    have hidx : k/base.length*base.length+k%base.length=k := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod k base.length
    conv_lhs => rw [tuples_succ_right,← hidx]
    rw [getD_flatMap_uniform _ _ base.length (by simp) [] [] hi hr]
    rw [List.getD_map_of_lt _ hr da []]
    rw [ih _ hq]
    simp only [indices,List.map_append,List.map_cons,List.map_nil]

end ThreeSum.OutputDecodeOrder

end

universe u_1

theorem solution : ∀ {α : Type u_1} (base : List.{u_1} α) (da : α),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) (@List.length.{u_1} α base) →
    ∀ (J k : Nat),
      @LT.lt.{0} Nat instLTNat k
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@List.length.{u_1} α base) J) →
        @Eq.{u_1 + 1} (List.{u_1} α)
          (@List.getD.{u_1} (List.{u_1} α) (@ThreeSum.RadixKeyLists.tuples.{u_1} α base J) k (@List.nil.{u_1} α))
          (@List.map.{0, u_1} Nat α (fun (i : Nat) => @List.getD.{u_1} α base i da)
            (ThreeSum.OutputDecodeOrder.indices (@List.length.{u_1} α base) J k)) := by
  exact @ThreeSum.OutputDecodeOrder.tuples_getD_indices_sourceProof

#print axioms solution
