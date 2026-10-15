-- Prove2me | solution 1 for ThreeSum.WeightEnumeration.coordinates_idxOf
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:51:19.328563+00:00
-- url     : https://prove2.me/submissions/a31f9fa4-2df3-41b0-82ac-12aa2aceedcd

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments

section


/-!
# Ordered radix enumeration of local hash coefficients

The Cartesian-product list used by `allWeights` enumerates the first
coordinate most slowly. The radix index consequently stores that coordinate
in its most significant digit. The equality below is equality of lists,
including their order and repetitions, rather than a membership equivalence.
-/

namespace ThreeSum.WeightEnumeration

open LocalHashMoments

variable {ι K : Type*} [DecidableEq ι] [NatCast K]



































































theorem liftCoordinate_injective (L : ℕ) :
    Function.Injective (@liftCoordinate L) := by
  intro i j hij
  apply Prod.ext
  · exact Fin.succ_injective L (congrArg Prod.fst hij)
  · exact congrArg (fun z : Fin (L+1) × Bool => z.2) hij

theorem coordinates_succ (L : ℕ) :
    coordinates (L+1) = (0,false)::(0,true)::(coordinates L).map liftCoordinate := by
  simp only [coordinates,List.finRange_succ,List.flatMap_cons,List.flatMap_map,
    List.map_flatMap,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    liftCoordinate]




















theorem coordinates_idxOf_sourceProof {L : ℕ} (i : Fin L × Bool) :
    (coordinates L).idxOf i = coordinateIndex i := by
  rcases i with ⟨i,b⟩
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · cases b <;> simp [coordinates_succ,coordinateIndex]
    · have hmap : ((coordinates L).map liftCoordinate).idxOf (j.succ,b) =
          (coordinates L).idxOf (j,b) := by
        change ((coordinates L).map liftCoordinate).idxOf (liftCoordinate (j,b)) = _
        simp only [List.idxOf,List.findIdx_map,Function.comp_def,
          (liftCoordinate_injective L).beq_eq]
      have hne : (0 : Fin (L+1)) ≠ j.succ := by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_zero,Fin.val_succ] at hh
        omega
      rw [coordinates_succ]
      simp only [List.idxOf_cons,cond_eq_ite,beq_iff_eq,Prod.mk.injEq,hne,false_and,
        ite_false,hmap,ih j]
      unfold coordinateIndex
      simp only [Fin.val_succ]
      omega




































































end ThreeSum.WeightEnumeration

end


theorem solution : ∀ {L : Nat} (i : Prod.{0, 0} (Fin L) Bool),
  @Eq.{1} Nat
    (@List.idxOf.{0} (Prod.{0, 0} (Fin L) Bool)
      (@instBEqProd.{0, 0} (Fin L) Bool (@instBEqOfDecidableEq.{0} (Fin L) (instDecidableEqFin L))
        (@instBEqOfDecidableEq.{0} Bool instDecidableEqBool))
      i (ThreeSum.LocalHashMoments.coordinates L))
    (@ThreeSum.WeightEnumeration.coordinateIndex L i) := by
  exact @ThreeSum.WeightEnumeration.coordinates_idxOf_sourceProof

#print axioms solution
