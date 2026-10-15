-- Prove2me | solution 1 for ThreeSum.CyclicFold.cyclic_correlation
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:43:07.02818+00:00
-- url     : https://prove2.me/submissions/f457af9a-7ffe-4784-8fba-a15001235bb3

import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba

section


/-!
# Folding a dense polynomial product into a cyclic convolution

The product of two vectors of length at most `p` has only two possible
contributions to an output residue `r < p`: coefficients `r` and `r+p`.
The double sum below specifies the answer; the implementation obtains it
by one fast product and a linear pass over the output coefficients.
-/

namespace ThreeSum.CyclicFold

open Finset Polynomial Karatsuba
open scoped BigOperators


















































theorem vector_length (p : ℕ) (f : ZMod p → ℕ) : (vector p f).length = p := by
  simp [vector]

theorem vector_getD (p : ℕ) (f : ZMod p → ℕ) (i : ℕ) (hi : i < p) :
    (vector p f).getD i 0 = (f (i : ZMod p) : ℤ) := by
  rw [List.getD_eq_getElem (vector p f) 0 (by rw [vector_length]; exact hi)]
  simp only [vector, List.getElem_map, List.getElem_range]

theorem sum_range_zmod {p : ℕ} [NeZero p] (f : ZMod p → ℤ) :
    (∑ i ∈ Finset.range p, f (i : ZMod p)) = ∑ i : ZMod p, f i := by
  apply Finset.sum_bij (fun (i : ℕ) (_ : i ∈ Finset.range p) => (i : ZMod p))
  · intro i hi
    exact mem_univ _
  · intro i hi j hj heq
    have h := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast_of_lt (mem_range.mp hi),
      ZMod.val_natCast_of_lt (mem_range.mp hj)] using h
  · intro z hz
    exact ⟨z.val, mem_range.mpr (ZMod.val_lt z), ZMod.natCast_zmod_val z⟩
  · intro i hi
    rfl

theorem cyclic_correlation_sourceProof {p : ℕ} [NeZero p]
    (F H : ZMod p → ℕ) (r : ℕ) (hr : r < p) :
    cyclic p (vector p F) (vector p (fun z => H (-z))) r =
      (Balancing.correlation F H (r : ZMod p) : ℤ) := by
  have heq (i j : ℕ) : (i + j) % p = r ↔
      (i : ZMod p) + (j : ZMod p) = (r : ZMod p) := by
    rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr]
  calc
    _ = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
        if (i : ZMod p) + (j : ZMod p) = (r : ZMod p)
        then (F (i : ZMod p) : ℤ) * (H (-(j : ZMod p)) : ℤ) else 0 := by
      unfold cyclic
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      simp only [vector_getD p F i (mem_range.mp hi),
        vector_getD p (fun z => H (-z)) j (mem_range.mp hj), heq]
    _ = ∑ i : ZMod p, ∑ j : ZMod p,
        if i + j = (r : ZMod p) then (F i : ℤ) * (H (-j) : ℤ) else 0 := by
      have hinner (i : ℕ) :
          (∑ j ∈ Finset.range p, if (i : ZMod p) + (j : ZMod p) = (r : ZMod p)
            then (F (i : ZMod p) : ℤ) * (H (-(j : ZMod p)) : ℤ) else 0) =
          ∑ j : ZMod p, if (i : ZMod p) + j = (r : ZMod p)
            then (F (i : ZMod p) : ℤ) * (H (-j) : ℤ) else 0 :=
        sum_range_zmod (fun j => if (i : ZMod p) + j = (r : ZMod p)
          then (F (i : ZMod p) : ℤ) * (H (-j) : ℤ) else 0)
      simp_rw [hinner]
      exact sum_range_zmod (fun i => ∑ j : ZMod p,
        if i + j = (r : ZMod p) then (F i : ℤ) * (H (-j) : ℤ) else 0)
    _ = ∑ i : ZMod p, (F i : ℤ) * (H (i - (r : ZMod p)) : ℤ) := by
      apply sum_congr rfl
      intro i hi
      have hj (j : ZMod p) : i + j = (r : ZMod p) ↔ j = (r : ZMod p) - i := by
        rw [eq_sub_iff_add_eq, add_comm]
      simp_rw [hj]
      simp
    _ = _ := by simp [Balancing.correlation]












































end ThreeSum.CyclicFold

end


theorem solution : ∀ {p : Nat} [inst : @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) p] (F H : ZMod p → Nat)
  (r : Nat),
  @LT.lt.{0} Nat instLTNat r p →
    @Eq.{1} Int
      (ThreeSum.CyclicFold.cyclic p (ThreeSum.CyclicFold.vector p F)
        (ThreeSum.CyclicFold.vector p fun (z : ZMod p) =>
          H
            (@Neg.neg.{0} (ZMod p)
              (@NegZeroClass.toNeg.{0} (ZMod p)
                (@SubNegZeroMonoid.toNegZeroClass.{0} (ZMod p)
                  (@SubtractionMonoid.toSubNegZeroMonoid.{0} (ZMod p)
                    (@SubtractionCommMonoid.toSubtractionMonoid.{0} (ZMod p)
                      (@AddCommGroup.toDivisionAddCommMonoid.{0} (ZMod p)
                        (@Ring.toAddCommGroup.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p))))))))
              z))
        r)
      (@Nat.cast.{0} Int instNatCastInt
        (@ThreeSum.Balancing.correlation.{0} (ZMod p)
          (@Ring.toAddCommGroup.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p))) (@ZMod.fintype p inst) F
          H
          (@Nat.cast.{0} (ZMod p)
            (@AddMonoidWithOne.toNatCast.{0} (ZMod p)
              (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod p)
                (@Ring.toAddGroupWithOne.{0} (ZMod p) (@CommRing.toRing.{0} (ZMod p) (ZMod.commRing p)))))
            r))) := by
  exact @ThreeSum.CyclicFold.cyclic_correlation_sourceProof

#print axioms solution
