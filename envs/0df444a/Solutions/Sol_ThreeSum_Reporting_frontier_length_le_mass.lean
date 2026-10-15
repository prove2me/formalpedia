-- Prove2me | solution 1 for ThreeSum.Reporting.frontier_length_le_mass
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:24:03.925892+00:00
-- url     : https://prove2.me/submissions/bd17d1e4-55a6-4497-ae47-0da1529e7863

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_Reporting_frontier_nodup
import Theorems.Thm_ThreeSum_Reporting_mem_frontier_iff


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Exact subset identities used by the proposed 3SUM algorithm

This module proves the algebraic identities, rather than taking the claimed
algorithm or its running time as an assumption.  `zeta` is the ordinary finite
subset sum; `mobius` is its signed inverse.  The fixed-cardinality specialization
is the identity used by the repeated histogram construction.
-/

namespace ThreeSum.Subset

open scoped BigOperators

variable {α : Type*} [DecidableEq α]































































































































































































































































/-! ## Stored partial zeta stages -/































































































































































































/-! ## Prefix reporting mass -/






/-- Refinement into all allowed next labels preserves the original weighted
mass, including multiplicity. This is a finite-sum identity, not a bound assumed
from the proposed 3SUM algorithm. -/
theorem fiberMass_conservation {β γ : Type*} [DecidableEq γ]
    (domain : Finset β) (labels : Finset γ) (label : β → γ) (weight : β → ℕ)
    (hlabels : ∀ p ∈ domain, label p ∈ labels) :
    (∑ value ∈ labels, fiberMass domain label weight value) =
      ∑ p ∈ domain, weight p := by
  exact Finset.sum_fiberwise_of_maps_to hlabels weight

/-- A positive child has integer mass at least one, so the number of positive
children cannot exceed the parent's mass. -/
theorem positive_fibers_le_mass {β γ : Type*} [DecidableEq γ]
    (domain : Finset β) (labels : Finset γ) (label : β → γ) (weight : β → ℕ)
    (hlabels : ∀ p ∈ domain, label p ∈ labels) :
    (labels.filter (fun value => 0 < fiberMass domain label weight value)).card ≤
      ∑ p ∈ domain, weight p := by
  rw [← fiberMass_conservation domain labels label weight hlabels]
  calc
    _ = ∑ value ∈ labels, if 0 < fiberMass domain label weight value then 1 else 0 := by
      simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro value hvalue
      split_ifs with h
      · omega
      · exact Nat.zero_le _



























end ThreeSum.Subset

end

section


/-!
# Executable positive-prefix reporting

The routine enumerates children of the current positive frontier and discards
zero counts. Its correctness interface asks for exact natural prefix counts;
the subset-transform identities supply those counts in the application.
No bound on the cost of obtaining a count is assumed or proved here.
-/

namespace ThreeSum.Reporting

open Finset
open scoped BigOperators

variable {ι α : Type*} [DecidableEq α]





theorem mass_pos_iff (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (k : ℕ) (pre : List α) :
    0 < mass I word weight k pre ↔
      ∃ i ∈ I, (word i).take k = pre ∧ 0 < weight i := by
  unfold mass Subset.fiberMass
  rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [mem_filter]
  constructor
  · rintro ⟨i, ⟨hi, hpre⟩, hw⟩
    exact ⟨i, hi, hpre, hw⟩
  · rintro ⟨i, hi, hpre, hw⟩
    exact ⟨i, ⟨hi, hpre⟩, hw⟩

























































































/-- The list is precisely the positive fibers, so its size is bounded by
the root mass, even if different raw incidences have the same value. -/
theorem frontier_length_le_mass_sourceProof (I : Finset ι) (word : ι → List α) (weight : ι → ℕ)
    (children : ℕ → List α) (query : ℕ → List α → ℕ) (J k : ℕ)
    (hlen : ∀ i ∈ I, (word i).length = J)
    (hchildren : ∀ i (hi : i ∈ I), ∀ j (hj : j < J),
      (word i)[j]'(by rw [hlen i hi]; exact hj) ∈ children j)
    (hquery : ∀ j ≤ J, ∀ pre, query j pre = mass I word weight j pre)
    (hc : ∀ k, (children k).Nodup) (hk : k ≤ J) :
    (frontier children query k).length ≤ ∑ i ∈ I, weight i := by
  classical
  let labels := I.image fun i => (word i).take k
  have heq : (frontier children query k).toFinset =
      labels.filter (fun pre => 0 < mass I word weight k pre) := by
    ext pre
    rw [List.mem_toFinset, mem_frontier_iff I word weight children query J k
      hlen hchildren hquery hk, mem_filter]
    constructor
    · intro h
      obtain ⟨i, hi, hpre, hw⟩ := (mass_pos_iff I word weight k pre).mp h
      exact ⟨mem_image.mpr ⟨i, hi, hpre⟩, h⟩
    · exact And.right
  have hcount := Subset.positive_fibers_le_mass I labels
    (fun i => (word i).take k) weight (fun i hi => mem_image.mpr ⟨i, hi, rfl⟩)
  change (labels.filter (fun pre => 0 < mass I word weight k pre)).card ≤ _ at hcount
  rw [← heq, List.toFinset_card_of_nodup (frontier_nodup children query hc k)] at hcount
  exact hcount










end ThreeSum.Reporting

end

universe u_1 u_2

theorem solution : ∀ {ι : Type u_1} {α : Type u_2} [inst : DecidableEq.{u_2 + 1} α] (I : Finset.{u_1} ι) (word : ι → List.{u_2} α)
  (weight : ι → Nat) (children : Nat → List.{u_2} α) (query : Nat → List.{u_2} α → Nat) (J k : Nat)
  (hlen :
    ∀ (i : ι),
      @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) I i →
        @Eq.{1} Nat (@List.length.{u_2} α (word i)) J),
  (∀ (i : ι)
      (hi :
        @Membership.mem.{u_1, u_1} ι (Finset.{u_1} ι)
          (@SetLike.instMembership.{u_1, u_1} (Finset.{u_1} ι) ι (@Finset.instSetLike.{u_1} ι)) I i)
      (j : Nat) (hj : @LT.lt.{0} Nat instLTNat j J),
      @Membership.mem.{u_2, u_2} α (List.{u_2} α) (@List.instMembership.{u_2} α) (children j)
        (@GetElem.getElem.{u_2, 0, u_2} (List.{u_2} α) Nat α
          (fun (as : List.{u_2} α) (i : Nat) => @LT.lt.{0} Nat instLTNat i (@List.length.{u_2} α as))
          (@List.instGetElemNatLtLength.{u_2} α) (word i) j
          (@Eq.mpr.{0} (@LT.lt.{0} Nat instLTNat j (@List.length.{u_2} α (word i))) (@LT.lt.{0} Nat instLTNat j J)
            (@id.{0}
              (@Eq.{1} Prop (@LT.lt.{0} Nat instLTNat j (@List.length.{u_2} α (word i))) (@LT.lt.{0} Nat instLTNat j J))
              (@congrArg.{1, 1} Nat Prop (@List.length.{u_2} α (word i)) J
                (fun (_a : Nat) => @LT.lt.{0} Nat instLTNat j _a) (hlen i hi)))
            hj))) →
    (∀ (j : Nat),
        @LE.le.{0} Nat instLENat j J →
          ∀ (pre : List.{u_2} α),
            @Eq.{1} Nat (query j pre) (@ThreeSum.Reporting.mass.{u_1, u_2} ι α inst I word weight j pre)) →
      (∀ (k : Nat), @List.Nodup.{u_2} α (children k)) →
        @LE.le.{0} Nat instLENat k J →
          @LE.le.{0} Nat instLENat
            (@List.length.{u_2} (List.{u_2} α) (@ThreeSum.Reporting.frontier.{u_2} α children query k))
            (∑ i ∈ I, weight i) := by
  exact @ThreeSum.Reporting.frontier_length_le_mass_sourceProof

#print axioms solution
