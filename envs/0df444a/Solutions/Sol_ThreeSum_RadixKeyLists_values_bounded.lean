-- Prove2me | solution 1 for ThreeSum.RadixKeyLists.values_bounded
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:50:10.006882+00:00
-- url     : https://prove2.me/submissions/d1ac022f-2575-436c-9e58-2198c596ec05

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle04
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
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.TakeDrop
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

section


/-!
# Exact product-list semantics for global radix-key construction

The key list retains every local occurrence, even when several records have
the same integer key. Each stage prepends one local record and computes its
positional hash. This is the order used by the concrete row constructor.
-/

namespace ThreeSum.RadixKeyLists

variable {α β : Type*}






















































































theorem values_bounded_sourceProof (p U : ℕ) (base : List ℤ)
    (hbase : ∀ x ∈ base, |x| ≤ (U : ℤ)) (j : ℕ) :
    ∀ z ∈ values (p : ℤ) base j, |z| ≤ ((U*(p+1)^j : ℕ) : ℤ) := by
  induction j with
  | zero =>
    intro z hz
    have hz0 : z=0 := by simpa only [values,List.mem_singleton] using hz
    subst z
    simp
  | succ j ih =>
    intro z hz
    obtain ⟨a,ha,hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hz
    have hkey := hbase a ha
    have htail := ih y hy
    have hpow : 1 ≤ (p+1)^j := one_le_pow₀ (by omega)
    have hU : (U : ℤ) ≤ ((U*(p+1)^j : ℕ) : ℤ) := by
      exact_mod_cast (Nat.le_mul_of_pos_right U (by omega : 0 < (p+1)^j))
    calc
      |a+(p : ℤ)*y| ≤ |a|+(p : ℤ)*|y| := by
        simpa only [abs_mul,Int.abs_natCast] using abs_add_le a ((p : ℤ)*y)
      _ ≤ (U : ℤ)+(p : ℤ)*((U*(p+1)^j : ℕ) : ℤ) :=
        add_le_add hkey (mul_le_mul_of_nonneg_left htail (Int.natCast_nonneg _))
      _ ≤ ((U*(p+1)^j : ℕ) : ℤ)+(p : ℤ)*((U*(p+1)^j : ℕ) : ℤ) :=
        add_le_add hU le_rfl
      _ = ((U*(p+1)^(j+1) : ℕ) : ℤ) := by push_cast; rw [pow_succ]; ring

end ThreeSum.RadixKeyLists

end


theorem solution : ∀ (p U : Nat) (base : List.{0} Int),
  (∀ (x : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int) base x →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup x)
          (@Nat.cast.{0} Int instNatCastInt U)) →
    ∀ (j : Nat) (z : Int),
      @Membership.mem.{0, 0} Int (List.{0} Int) (@List.instMembership.{0} Int)
          (ThreeSum.RadixKeyLists.values (@Nat.cast.{0} Int instNatCastInt p) base j) z →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup z)
          (@Nat.cast.{0} Int instNatCastInt
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) U
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                j))) := by
  exact @ThreeSum.RadixKeyLists.values_bounded_sourceProof

#print axioms solution
