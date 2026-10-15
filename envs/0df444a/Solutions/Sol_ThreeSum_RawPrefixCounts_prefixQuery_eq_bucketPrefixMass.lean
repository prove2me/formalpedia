-- Prove2me | solution 1 for ThreeSum.RawPrefixCounts.prefixQuery_eq_bucketPrefixMass
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:43:25.340591+00:00
-- url     : https://prove2.me/submissions/91de3ea4-cfe3-4a91-a508-c7b59ec6392d

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
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
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Radix_mem_representations


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting

section


/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments


























































































































































theorem mem_representations (h J : ℕ) (a b : ℤ) (xs : List (RetainedChoice h)) :
    xs ∈ representations h J a b ↔ xs.length = J ∧
      globalModulus h J ∣ a - Radix.positionalHash (localPrime h) rawLeft xs ∧
      globalModulus h J ∣ b - Radix.positionalHash (localPrime h) rawRight xs := by
  exact Radix.mem_representations (localPrime h)
    (by exact_mod_cast (localPrime_pos h).ne') rawLeft rawRight J a b xs




























































































































end ThreeSum.GlobalEncoding

end

section


/-!
# Original-index incidences in the guarded global encoding

An incidence retains its original input indices, its complete sequence of
chosen-map occurrences and retained local edges, and its signed arithmetic
lift. Equal input values remain distinct original indices. The lift is
unique for a fixed original triple and representation, so it does not add
a factor of three to the representation bound.
-/

namespace ThreeSum.RawIncidences

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds































































































theorem tuple_mem_representations {h J : ℕ} (t : ChoiceTuple h J) (b c : ℤ) :
    List.ofFn t ∈ representations h J b c ↔
      globalModulus h J ∣ b - tupleLeft t ∧ globalModulus h J ∣ c - tupleRight t := by
  rw [mem_representations]
  simp only [List.length_ofFn, true_and, tupleLeft, tupleRight]




















theorem mem_witnesses {h J : ℕ} {P d a b c : ℤ} {w : Witness h J} :
    w ∈ witnesses h J P d a b c ↔
      List.ofFn w.1 ∈ representations h J (b % P) (c % P + d) ∧
        globalModulus h J ∣ (a % P + lift w.2 * P + d) - tupleKey w.1 := by
  simp only [witnesses, Finset.mem_filter, Finset.mem_univ, true_and]



































































































section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]














theorem mem_rawOn {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : RawItem h J α β γ} :
    r ∈ rawOn h J P d T a b c ↔
      r.1 ∈ T ∧ r.2 ∈ witnesses h J P d (a r.1.1) (b r.1.2.1) (c r.1.2.2) :=
  Finset.mem_sigma












































































theorem bucket_product_eq_sum {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : ChoiceTuple h J) :
    leftBucket P B b t * rightBucket P d C c t =
      ∑ j ∈ B, ∑ k ∈ C,
        if globalModulus h J ∣ b j % P - tupleLeft t ∧
          globalModulus h J ∣ c k % P + d - tupleRight t then 1 else 0 := by
  unfold leftBucket rightBucket
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hL : globalModulus h J ∣ b j % P - tupleLeft t <;>
    by_cases hR : globalModulus h J ∣ c k % P + d - tupleRight t <;> simp [hL, hR]

theorem bucket_product_eq_card {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : ChoiceTuple h J) :
    leftBucket P B b t * rightBucket P d C c t =
      ((B ×ˢ C).filter fun p => globalModulus h J ∣ b p.1 % P - tupleLeft t ∧
        globalModulus h J ∣ c p.2 % P + d - tupleRight t).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  exact bucket_product_eq_sum P d B C b c t





































































































end OriginalIndices

end ThreeSum.RawIncidences

end

section


/-!
# Exact bucket products at a wanted reporting prefix

The raw fiber used by the reporting theorem is here expanded into independently
counted B and C buckets. The wanted query fixes its original A index, lift,
and all chosen-map occurrences and output subsets.
-/

namespace ThreeSum.RawPrefixCounts

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding RawIncidences RawReporting

section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]





theorem prefixQuery_eq_card {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (k : ℕ) (pre : List (Finset (Fin (512 * h)))) :
    prefixQuery I w k pre = (prefixItems I w k pre).card := by
  simp only [prefixQuery, Reporting.mass, Subset.fiberMass, prefixItems,
    Finset.sum_const, smul_eq_mul, mul_one]














private theorem pack_injective {h J : ℕ} (w : Wanted h J α) :
    Function.Injective (pack (β := β) (γ := γ) w) := by
  intro s t he
  apply Sigma.ext
  · exact congrArg (fun r => r.2.1) he
  · exact heq_of_eq (congrArg (fun r => r.1.2) he)

private theorem pack_unpack {h J : ℕ} (w : Wanted h J α) (r : RawItem h J α β γ)
    (hw : wantedOf r = w) : pack w ⟨r.2.1, r.1.2⟩ = r := by
  rw [← hw]
  rfl

private theorem pack_mem_prefixItems {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h))))
    (s : Σ _t : ChoiceTuple h J, β × γ) :
    pack w s ∈ prefixItems (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre ↔
      (w.1 ∈ A ∧ globalModulus h J ∣
        (a w.1 % P + lift w.2.1 * P + d) - globalKey w.2.2) ∧
      s.1 ∈ completions w.2.2 k pre ∧ s.2 ∈ compatiblePairs P d B C b c s.1 := by
  constructor
  · intro hr
    obtain ⟨hd, hpre⟩ := Finset.mem_filter.mp hr
    obtain ⟨hraw, hw⟩ := Finset.mem_filter.mp hd
    obtain ⟨hm, hrep, hkey⟩ := (mem_rawOn.mp hraw).imp_right mem_witnesses.mp
    have hq : tupleOutput s.1 = w.2.2 := congrArg (fun z => z.2.2) hw
    have hke : tupleKey s.1 = globalKey w.2.2 := congrArg globalKey hq
    have hpair := (tuple_mem_representations s.1 (b s.2.1 % P)
      (c s.2.2 % P + d)).mp hrep
    have hm' : w.1 ∈ A ∧ s.2 ∈ B ×ˢ C := Finset.mem_product.mp hm
    refine ⟨⟨hm'.1, ?_⟩, ?_, ?_⟩
    · simpa only [pack, hke] using hkey
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, hpre⟩
    · exact Finset.mem_filter.mpr ⟨hm'.2, hpair⟩
  · rintro ⟨⟨ha, hkey⟩, ht, hp⟩
    obtain ⟨_, hq, hpre⟩ := Finset.mem_filter.mp ht
    obtain ⟨hm, hpair⟩ := Finset.mem_filter.mp hp
    have hke : tupleKey s.1 = globalKey w.2.2 := congrArg globalKey hq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, hpre⟩
    · apply mem_rawOn.mpr
      refine ⟨Finset.mem_product.mpr ⟨ha, hm⟩, mem_witnesses.mpr ⟨?_, ?_⟩⟩
      · exact (tuple_mem_representations s.1 _ _).mpr hpair
      · simpa only [pack, hke] using hkey
    · exact Prod.ext rfl (Prod.ext rfl hq)












theorem prefixQuery_eq_bucketPrefixMass_sourceProof {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) :
    prefixQuery (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre =
      bucketPrefixMass P d A B C a b c w k pre := by
  rw [prefixQuery_eq_card, bucketPrefixMass]
  split
  next hguard =>
    let pairs := (completions w.2.2 k pre).sigma fun t => compatiblePairs P d B C b c t
    have he : pairs.card =
        (prefixItems (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre).card := by
      apply Finset.card_bij (fun s _ => pack w s)
      · intro s hs
        exact (pack_mem_prefixItems P d A B C a b c w k pre s).mpr
          ⟨hguard, (Finset.mem_sigma.mp hs).1, (Finset.mem_sigma.mp hs).2⟩
      · intro s _ t _ he
        exact pack_injective w he
      · intro r hr
        have hw := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
        let s : Σ _t : ChoiceTuple h J, β × γ := ⟨r.2.1, r.1.2⟩
        have he : pack w s = r := pack_unpack w r hw
        refine ⟨s, ?_, he⟩
        have hs := (pack_mem_prefixItems P d A B C a b c w k pre s).mp (he ▸ hr)
        exact Finset.mem_sigma.mpr hs.2
    rw [← he, Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro t _
    exact (bucket_product_eq_card P d B C b c t).symm
  next hguard =>
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hw := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
    have he := pack_unpack w r hw
    have hs := (pack_mem_prefixItems P d A B C a b c w k pre ⟨r.2.1, r.1.2⟩).mp
      (he ▸ hr)
    exact hguard hs.1

end Indices

end ThreeSum.RawPrefixCounts

end

universe u_1 u_2 u_3

theorem solution : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [Fintype.{u_1} α] [Fintype.{u_2} β] [Fintype.{u_3} γ]
  [inst : DecidableEq.{u_1 + 1} α] [DecidableEq.{u_2 + 1} β] [DecidableEq.{u_3 + 1} γ] {h J : Nat} (P d : Int)
  (A : Finset.{u_1} α) (B : Finset.{u_2} β) (C : Finset.{u_3} γ) (a : α → Int) (b : β → Int) (c : γ → Int)
  (w : ThreeSum.RawReporting.Wanted.{u_1} h J α) (k : Nat)
  (pre :
    List.{0}
      (Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))),
  @Eq.{1} Nat
    (@ThreeSum.RawReporting.prefixQuery.{u_1, u_2, u_3} α β γ inst h J
      (@ThreeSum.RawIncidences.rawOn.{u_1, u_2, u_3} α β γ h J P d
        (@SProd.sprod.{u_1, max u_2 u_3, max (max u_1 u_2) u_3} (Finset.{u_1} α)
          (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ))
          (Finset.{max (max u_2 u_3) u_1} (Prod.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)))
          (@Finset.instSProd.{u_1, max u_2 u_3} α (Prod.{u_2, u_3} β γ)) A
          (@SProd.sprod.{u_2, u_3, max u_2 u_3} (Finset.{u_2} β) (Finset.{u_3} γ)
            (Finset.{max u_3 u_2} (Prod.{u_2, u_3} β γ)) (@Finset.instSProd.{u_2, u_3} β γ) B C))
        a b c)
      w k pre)
    (@ThreeSum.RawPrefixCounts.bucketPrefixMass.{u_1, u_2, u_3} α β γ inst h J P d A B C a b c w k pre) := by
  exact @ThreeSum.RawPrefixCounts.prefixQuery_eq_bucketPrefixMass_sourceProof

#print axioms solution
