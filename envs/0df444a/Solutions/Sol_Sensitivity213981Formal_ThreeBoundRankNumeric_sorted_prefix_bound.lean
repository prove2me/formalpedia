-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.sorted_prefix_bound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T18:34:36.638465+00:00
-- url     : https://prove2.me/submissions/e93a7b1c-94a7-43b7-9c66-bc558e3846fb

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_RankSmallAverage
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


namespace Sensitivity213981Formal
section
/- Exact integer averaging for sorted residual weights and actual marker subsets. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRankNumeric
open scoped BigOperators



/-- The arithmetic step uses a boundary weight x between the chosen prefix
and its complement.  This form has no bound on the number of entries. -/
theorem prefix_allowance_bound (m n p e x : ℕ) (hm : m ≤  n)
    (hp : p ≤  m*x) (ht : p+(n-m)*x ≤  e) : p ≤  allowance m e n := by
  by_cases hx : x ≤  e/n
  · exact (hp.trans (Nat.mul_le_mul_left m hx)).trans (Nat.le_add_right _ _)
  · have hx' : e/n+1 ≤  x := by omega
    have ht' := (Nat.add_le_add_left (Nat.mul_le_mul_left (n-m) hx') p).trans ht
    have hmul : m*(e/n)+(n-m)*(e/n)=n*(e/n) := by
      rw [← Nat.add_mul,Nat.add_sub_of_le hm]
    have hdiv := Nat.div_add_mod e n
    simp only [Nat.mul_add,Nat.mul_one] at ht'
    unfold allowance
    omega

/-- The sharp integer average bound for the m smallest weights. -/
theorem sorted_prefix_bound (xs : List ℕ) (hs : xs.Pairwise (· ≤  ·))
    (m : ℕ) (hm : m ≤  xs.length) :
    (xs.take m).sum ≤  allowance m xs.sum xs.length := by
  let x := (xs.take m).toFinset.sup id
  have hp : (xs.take m).sum ≤  m*x := by
    have hh := List.sum_le_card_nsmul (xs.take m) x (fun y hy =>
      Finset.le_sup (f:=id) (List.mem_toFinset.mpr hy))
    simpa only [List.length_take,min_eq_left hm,nsmul_eq_mul,Nat.cast_id] using hh
  have ht : (xs.length-m)*x ≤  (xs.drop m).sum := by
    have hh := List.card_nsmul_le_sum (xs.drop m) x (fun y hy => by
      apply Finset.sup_le
      intro z hz
      exact hs.rel_of_mem_take_of_mem_drop (List.mem_toFinset.mp hz) hy)
    simpa only [List.length_drop,nsmul_eq_mul,Nat.cast_id] using hh
  have he : (xs.take m).sum+(xs.drop m).sum=xs.sum := by
    rw [← List.sum_append,List.take_append_drop]
  exact prefix_allowance_bound m xs.length (xs.take m).sum xs.sum x hm hp
    ((Nat.add_le_add_left ht _).trans_eq he)









end ThreeBoundRankNumeric





end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (xs : List.{0} Nat) (hs : @List.Pairwise.{0} Nat (fun (x1 x2 : Nat) => @LE.le.{0} Nat instLENat x1 x2) xs) (m : Nat)
  (hm : @LE.le.{0} Nat instLENat m (@List.length.{0} Nat xs)),
  @LE.le.{0} Nat instLENat
    (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (@List.take.{0} Nat m xs))
    (Sensitivity213981Formal.ThreeBoundRankNumeric.allowance m
      (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) xs) (@List.length.{0} Nat xs)) := @Sensitivity213981Formal.ThreeBoundRankNumeric.sorted_prefix_bound
