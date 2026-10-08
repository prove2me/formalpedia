-- Prove2me | solution 1 for PrimePairSieve.reciprocal_mass_endpoint_sound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T21:20:49.168812+00:00
-- url     : https://prove2.me/submissions/0be15da8-1276-4b1a-a399-a4226ac0a989

import Definitions.Def_PrimePairSieve_ReciprocalMass
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped BigOperators
set_option autoImplicit false
namespace ReciprocalBucketTransfer

/-- Integer division rounds a scaled bucket contribution down. -/
lemma rounded_mass_le (S L U M : ℕ) (hS : 0 < S) (hL : 0 < L) :
    ((M * L / (L + U) : ℕ) : ℝ) / S ≤
      ((M : ℝ) / S) / (1 + (U : ℝ) / L) := by
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hl : (0 : ℝ) < L := by exact_mod_cast hL
  have hu : (0 : ℝ) ≤ U := Nat.cast_nonneg U
  have hround : (((M * L / (L + U) : ℕ) : ℝ)) * (L + U) ≤ (M : ℝ) * L := by
    exact_mod_cast Nat.div_mul_le_self (M * L) (L + U)
  have heq : ((M : ℝ) / S) / (1 + (U : ℝ) / L) =
      (M : ℝ) * L / ((S : ℝ) * (L + U)) := by
    field_simp
  rw [heq]
  apply (div_le_div_iff₀ hs (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hround hs.le]

/-- A mass lower bound remains valid after replacing every denominator in a
bucket by the denominator at its upper index. -/
lemma bucket_lower (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (s : Finset ℕ) (S L U M : ℕ) (hS : 0 < S) (hL : 0 < L)
    (hupper : ∀ n ∈ s, n ≤ U)
    (hmass : (M : ℝ) / S ≤ ∑ n ∈ s, c n) :
    ((M * L / (L + U) : ℕ) : ℝ) / S ≤
      ∑ n ∈ s, c n / (1 + (n : ℝ) / L) := by
  have hl : (0 : ℝ) < L := by exact_mod_cast hL
  calc
    _ ≤ ((M : ℝ) / S) / (1 + (U : ℝ) / L) := rounded_mass_le S L U M hS hL
    _ ≤ (∑ n ∈ s, c n) / (1 + (U : ℝ) / L) :=
      div_le_div_of_nonneg_right hmass (by positivity)
    _ = ∑ n ∈ s, c n / (1 + (U : ℝ) / L) := Finset.sum_div _ _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      apply div_le_div_of_nonneg_left (hc n) (by positivity)
      exact add_le_add le_rfl
        (div_le_div_of_nonneg_right (by exact_mod_cast hupper n hn) hl.le)

/-- Disjoint checked buckets may be added without counting a weight twice.
Incomplete buckets can be omitted by choosing a smaller index set. -/
theorem buckets_lower {ι : Type*} [DecidableEq ι]
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (buckets : Finset ι) (indices : ι → Finset ℕ)
    (upper mass : ι → ℕ) (S L : ℕ) (hS : 0 < S) (hL : 0 < L)
    (hdisjoint : (buckets : Set ι).PairwiseDisjoint indices)
    (hsubset : ∀ i ∈ buckets, indices i ⊆ Finset.Icc 1 L)
    (hupper : ∀ i ∈ buckets, ∀ n ∈ indices i, n ≤ upper i)
    (hmass : ∀ i ∈ buckets, (mass i : ℝ) / S ≤ ∑ n ∈ indices i, c n) :
    ∑ i ∈ buckets, ((mass i * L / (L + upper i) : ℕ) : ℝ) / S ≤
      ∑ n ∈ Finset.Icc 1 L, c n / (1 + (n : ℝ) / L) := by
  have hcover : buckets.biUnion indices ⊆ Finset.Icc 1 L := by
    intro n hn
    obtain ⟨i, hi, hn⟩ := Finset.mem_biUnion.mp hn
    exact hsubset i hi hn
  calc
    _ ≤ ∑ i ∈ buckets, ∑ n ∈ indices i, c n / (1 + (n : ℝ) / L) := by
      apply Finset.sum_le_sum
      intro i hi
      exact bucket_lower c hc (indices i) S L (upper i) (mass i) hS hL
        (hupper i hi) (hmass i hi)
    _ = ∑ n ∈ buckets.biUnion indices, c n / (1 + (n : ℝ) / L) :=
      (Finset.sum_biUnion hdisjoint).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hcover
      (fun n _ _ => div_nonneg (hc n) (by positivity))


end ReciprocalBucketTransfer

namespace PrimePairSieve.ReciprocalBatch
lemma nonneg (n : ℕ) : 0 ≤ weight n := by
  unfold weight
  split_ifs
  · apply Finset.prod_nonneg
    intro p hp
    split_ifs with h2
    · norm_num
    · have h3 : 3 ≤ p := by
        have := (Nat.prime_of_mem_primeFactors hp).two_le
        omega
      have h3R : (3:ℝ) ≤ p := by exact_mod_cast h3
      exact div_nonneg (by norm_num) (by linarith)
  · exact le_rfl


end PrimePairSieve.ReciprocalBatch
open PrimePairSieve

theorem solution (scale L : ℕ) (hs : 0 < scale) (hL : 0 < L)
    (buckets : Finset ReciprocalMass.Bucket)
    (hpositive : ∀ b ∈ buckets, 1 ≤ b.lower)
    (hdisjoint : ∀ a ∈ buckets, ∀ b ∈ buckets, a ≠ b →
      a.upper < b.lower ∨ b.upper < a.lower)
    (hmass : ReciprocalMass.Valid scale buckets) :
    (ReciprocalMass.endpointSum L buckets : ℝ) / scale ≤
      ∑ n ∈ Finset.Icc 1 L, ReciprocalBatch.weight n / (1 + (n : ℝ) / L) := by
  let chosen := buckets.filter (fun b => b.upper ≤ L)
  have hsub (b : ReciprocalMass.Bucket) (hb : b ∈ chosen) : b ∈ buckets :=
    (Finset.mem_filter.mp hb).1
  have hupper (b : ReciprocalMass.Bucket) (hb : b ∈ chosen) : b.upper ≤ L :=
    (Finset.mem_filter.mp hb).2
  have hd : (chosen : Set ReciprocalMass.Bucket).PairwiseDisjoint
      (fun b => Finset.Icc b.lower b.upper) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro n hna hnb
    have hna' := Finset.mem_Icc.mp hna
    have hnb' := Finset.mem_Icc.mp hnb
    rcases hdisjoint a (hsub a ha) b (hsub b hb) hab with h | h <;> omega
  have h := ReciprocalBucketTransfer.buckets_lower ReciprocalBatch.weight
    ReciprocalBatch.nonneg chosen (fun b => Finset.Icc b.lower b.upper)
    ReciprocalMass.Bucket.upper ReciprocalMass.Bucket.mass scale L hs hL hd
    (fun b hb => Finset.Icc_subset_Icc (hpositive b (hsub b hb)) (hupper b hb))
    (fun b _ n hn => (Finset.mem_Icc.mp hn).2)
    (fun b hb => hmass b (hsub b hb))
  simpa only [ReciprocalMass.endpointSum, Nat.cast_sum, Finset.sum_div] using h
#print axioms solution
