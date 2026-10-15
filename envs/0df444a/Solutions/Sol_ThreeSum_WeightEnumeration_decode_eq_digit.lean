-- Prove2me | solution 1 for ThreeSum.WeightEnumeration.decode_eq_digit
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:51:18.544706+00:00
-- url     : https://prove2.me/submissions/7b40a5fa-bb7e-4bb4-8e79-bbad27ac3c4d

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







































theorem low_digit (p n e t : ℕ) (he : e < t) :
    (n%p^t)/p^e%p = n/p^e%p := by
  have hpow : p^t = p^e*p^(t-e) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow,Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (dvd_pow_self p (by omega : t-e ≠ 0))]

/-- Each coordinate is the digit at its first occurrence in the list. -/
theorem decode_eq_digit_sourceProof (p : ℕ) (l : List ι) (k : ℕ) (i : ι) (hi : i ∈ l) :
    decode (K := K) p l k i hi = ((k/p^(l.length-1-l.idxOf i)%p : ℕ) : K) := by
  induction l generalizing k i with
  | nil => simp at hi
  | cons a l ih =>
    by_cases hia : i = a
    · subst i
      simp [decode,List.Pi.cons_def]
    · have hil : i ∈ l := (List.mem_cons.mp hi).resolve_left hia
      have hidx : l.idxOf i < l.length := List.idxOf_lt_length_of_mem hil
      simp only [decode,List.Pi.cons_def,dif_neg hia]
      rw [ih (k%p^l.length) i hil,List.idxOf_cons_ne _ (Ne.symm hia)]
      simp only [List.length_cons,Nat.succ_sub_one]
      rw [show l.length-(l.idxOf i+1) = l.length-1-l.idxOf i by omega]
      exact congrArg (fun n : ℕ => (n : K)) (low_digit p k _ _ (by omega))































































































































end ThreeSum.WeightEnumeration

end

universe u_1 u_2

theorem solution : ∀ {ι : Type u_1} {K : Type u_2} [inst : DecidableEq.{u_1 + 1} ι] [inst_1 : NatCast.{u_2} K] (p : Nat) (l : List.{u_1} ι)
  (k : Nat) (i : ι) (hi : @Membership.mem.{u_1, u_1} ι (List.{u_1} ι) (@List.instMembership.{u_1} ι) l i),
  @Eq.{u_2 + 1} K (@ThreeSum.WeightEnumeration.decode.{u_1, u_2} ι K inst inst_1 p l k i hi)
    (@Nat.cast.{u_2} K inst_1
      (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
        (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) k
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (@List.length.{u_1} ι l)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@List.idxOf.{u_1} ι (@instBEqOfDecidableEq.{u_1} ι inst) i l))))
        p)) := by
  exact @ThreeSum.WeightEnumeration.decode_eq_digit_sourceProof

#print axioms solution
