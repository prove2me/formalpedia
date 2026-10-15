-- Prove2me | solution 1 for ThreeSum.WeightEnumeration.pi_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:51:01.907988+00:00
-- url     : https://prove2.me/submissions/20154462-abae-42a7-a498-9704db2f87ab

import Aesop
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

/-- Flattening consecutive fixed-width blocks gives the ordinary range. -/
theorem range_blocks (m q : ℕ) :
    (List.range m).flatMap (fun b => (List.range q).map (fun r => b*q+r)) =
      List.range (m*q) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.range_succ,List.flatMap_append,List.flatMap_singleton,ih,Nat.succ_mul]
    exact List.range_add.symm







theorem pi_eq_range_sourceProof (p : ℕ) (l : List ι) :
    List.pi l (fun _ => (List.range p).map (fun n : ℕ => (n : K))) =
      (List.range (p^l.length)).map (decode (K := K) p l) := by
  induction l with
  | nil => simp [decode]
  | cons i l ih =>
    rw [List.pi_cons,ih]
    simp only [List.flatMap_map,List.map_map,List.length_cons,pow_succ',← range_blocks,
      List.map_flatMap]
    apply List.flatMap_congr
    intro b hb
    have hbp : b < p := List.mem_range.mp hb
    apply List.map_congr_left
    intro r hr
    have hrq : r < p^l.length := List.mem_range.mp hr
    have hq : 0 < p^l.length := by omega
    have hdiv : (b*p^l.length+r)/p^l.length = b := by
      rw [Nat.add_comm,Nat.add_mul_div_right _ _ hq,Nat.div_eq_of_lt hrq]
      simp
    simp only [Function.comp_apply,decode,hdiv,Nat.mod_eq_of_lt hbp,
      Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hrq]

























































































































































end ThreeSum.WeightEnumeration

end

universe u_1 u_2

theorem solution : ∀ {ι : Type u_1} {K : Type u_2} [inst : DecidableEq.{u_1 + 1} ι] [inst_1 : NatCast.{u_2} K] (p : Nat)
  (l : List.{u_1} ι),
  @Eq.{max (u_1 + 1) (u_2 + 1)}
    (List.{max u_1 u_2} ((i : ι) → @Membership.mem.{u_1, u_1} ι (List.{u_1} ι) (@List.instMembership.{u_1} ι) l i → K))
    (@List.pi.{u_1, u_2} ι inst (fun (x : ι) => K) l fun (x : ι) =>
      @List.map.{0, u_2} Nat K (fun (n : Nat) => @Nat.cast.{u_2} K inst_1 n) (List.range p))
    (@List.map.{0, max u_1 u_2} Nat
      ((i : ι) → @Membership.mem.{u_1, u_1} ι (List.{u_1} ι) (@List.instMembership.{u_1} ι) l i → K)
      (@ThreeSum.WeightEnumeration.decode.{u_1, u_2} ι K inst inst_1 p l)
      (List.range
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
          (@List.length.{u_1} ι l)))) := by
  exact @ThreeSum.WeightEnumeration.pi_eq_range_sourceProof

#print axioms solution
