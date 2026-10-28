-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankNumeric.negative_weighted
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T19:30:53.936765+00:00
-- url     : https://prove2.me/submissions/be1ed0d4-bc10-4be7-b3ca-34a476b4c2d2

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCapData
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundGreedy_greedy_four
import Theorems.Thm_Sensitivity213981Formal_ThreeBoundGreedy_greedy_three


namespace Sensitivity213981Formal
section
/- Exact greedy allocation for the simultaneous negative-candidate prefix caps.
The hypotheses concern actual counts and decreasing costs.  No transfer
inequality is assumed. -/


set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundGreedy

theorem weighted_two_prefix (n₀ n₁ g₀ g₁ a₀ a₁ : ℕ)
    (h₀ : n₀ ≤  g₀) (h₁ : n₀+n₁ ≤  g₀+g₁) (ha : a₁ ≤  a₀) :
    n₀*a₀+n₁*a₁ ≤  g₀*a₀+g₁*a₁ := by
  let d := a₀-a₁
  have hd : a₀ = d+a₁ := (Nat.sub_add_cancel ha).symm
  rw [hd]
  calc
    n₀*(d+a₁)+n₁*a₁ = n₀*d+(n₀+n₁)*a₁ := by ring
    _ ≤  g₀*d+(g₀+g₁)*a₁ := Nat.add_le_add
      (Nat.mul_le_mul_right d h₀) (Nat.mul_le_mul_right a₁ h₁)
    _ = g₀*(d+a₁)+g₁*a₁ := by ring





/-- The two-level fill used at q=1 after removing the positive prefix. -/
theorem greedy_two (n₀ n₁ c₀ c₁ a₀ a₁ : ℕ)
    (h₀ : n₀ ≤  c₀) (h₁ : n₀+n₁ ≤  c₁) (ha : a₁ ≤  a₀) :
    n₀*a₀+n₁*a₁ ≤  min c₀ c₁*a₀+(c₁-min c₀ c₁)*a₁ := by
  apply weighted_two_prefix
  · exact le_min h₀ (by omega)
  · have hh := Nat.sub_add_cancel (min_le_right c₀ c₁)
    omega
  · exact ha









end ThreeBoundGreedy




end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- The exact negative allocation in the numeric recurrence dominates every
actual count vector satisfying its simultaneous prefix constraints. -/


set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundRankNumeric
open ThreeBoundNumeric ThreeBoundGreedy
open scoped BigOperators

theorem negative_weighted (caps : Caps) (perfect : ℕ) (r : Record) (e q : ℕ) (hq : q ≤  3)
    (count cost : ℕ → ℕ)
    (hp : ∀ k, k ≤  q → (∑ b ∈ Finset.range (k+1), count b) ≤ 
      convertedCap caps perfect r e k)
    (ha : ∀ k, k+1 ≤  q → cost (k+1) ≤  cost k) :
    (∑ b ∈ Finset.range (q+1), count b*cost b) ≤ 
      ((List.range (q+1)).map fun b => negativeCount caps perfect q r e b*cost b).sum := by
  have h0 := hp 0 (by omega)
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at h0
  interval_cases q
  · simpa [negativeCount,suffixCapacity,interval] using Nat.mul_le_mul_right (cost 0) h0
  · have h1 := hp 1 (by omega)
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at h1
    have hh := greedy_two (count 0) (count 1)
      (convertedCap caps perfect r e 0) (convertedCap caps perfect r e 1)
      (cost 0) (cost 1) h0 h1 (ha 0 (by omega))
    simpa [negativeCount,suffixCapacity,interval,List.range_succ,Finset.sum_range_succ,
      min_assoc,min_comm,min_left_comm,Nat.add_assoc] using hh
  · have h1 := hp 1 (by omega)
    have h2 := hp 2 (by omega)
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at h1 h2
    let c0 := convertedCap caps perfect r e 0
    let c1 := convertedCap caps perfect r e 1
    let c2 := convertedCap caps perfect r e 2
    have he : min c0 (min c1 c2)+(min c1 c2-min c0 (min c1 c2)) = min c1 c2 := by omega
    have hh := greedy_three (count 0) (count 1) (count 2) c0 c1 c2
      (cost 0) (cost 1) (cost 2) h0 h1 h2 (ha 0 (by omega)) (ha 1 (by omega))
    dsimp only at hh
    rw [he] at hh
    simpa [negativeCount,suffixCapacity,interval,List.range_succ,Finset.sum_range_succ,
      min_assoc,min_comm,min_left_comm,Nat.add_assoc,c0,c1,c2] using hh

  · have h1 := hp 1 (by omega)
    have h2 := hp 2 (by omega)
    have h3 := hp 3 (by omega)
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add] at h1 h2 h3
    let c0 := convertedCap caps perfect r e 0
    let c1 := convertedCap caps perfect r e 1
    let c2 := convertedCap caps perfect r e 2
    let c3 := convertedCap caps perfect r e 3
    have he0 : min c0 (min c1 (min c2 c3))+
        (min c1 (min c2 c3)-min c0 (min c1 (min c2 c3))) = min c1 (min c2 c3) := by omega
    have he1 : min c1 (min c2 c3)+(min c2 c3-min c1 (min c2 c3)) = min c2 c3 := by omega
    have hh := greedy_four (count 0) (count 1) (count 2) (count 3) c0 c1 c2 c3
      (cost 0) (cost 1) (cost 2) (cost 3) h0 h1 h2 h3
      (ha 0 (by omega)) (ha 1 (by omega)) (ha 2 (by omega))
    dsimp only at hh
    rw [he0,he1] at hh
    simpa [negativeCount,suffixCapacity,interval,List.range_succ,Finset.sum_range_succ,
      min_assoc,min_comm,min_left_comm,Nat.add_assoc,c0,c1,c2,c3] using hh

end ThreeBoundRankNumeric



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat)
  (r : Sensitivity213981Formal.ThreeBoundRankNumeric.Record) (e q : Nat)
  (hq : @LE.le.{0} Nat instLENat q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
  (count cost : Nat → Nat)
  (hp :
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat k q →
        @LE.le.{0} Nat instLENat
          (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid
            (Finset.range
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            fun (b : Nat) => count b)
          (Sensitivity213981Formal.ThreeBoundRankNumeric.convertedCap caps perfect r e k))
  (ha :
    ∀ (k : Nat),
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          q →
        @LE.le.{0} Nat instLENat
          (cost
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) k
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (cost k)),
  @LE.le.{0} Nat instLENat
    (@Finset.sum.{0, 0} Nat Nat Nat.instAddCommMonoid
      (Finset.range
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      fun (b : Nat) => @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (count b) (cost b))
    (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
      (@List.map.{0, 0} Nat Nat
        (fun (b : Nat) =>
          @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (Sensitivity213981Formal.ThreeBoundRankNumeric.negativeCount caps perfect q r e b) (cost b))
        (List.range
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) q
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) := @Sensitivity213981Formal.ThreeBoundRankNumeric.negative_weighted
