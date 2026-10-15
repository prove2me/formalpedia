-- Prove2me | solution 1 for ThreeSum.BlockForced.transformPrefixValue_eq_bucket_sum
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:43:26.181538+00:00
-- url     : https://prove2.me/submissions/ad281f29-6ffc-478d-b59c-719d90b2f669

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
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
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BlockForced_completed_bucket_sum
import Theorems.Thm_ThreeSum_Subset_forced_prefix_identity


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting

section


/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows

open Finset
open scoped BigOperators











@[simp] theorem mem_join {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma

@[simp] theorem mem_flat {J L : ℕ} {u : Fin J → Finset (Fin L)}
    {i : Fin J} {x : Fin L} : Sigma.mk i x ∈ flat u ↔ x ∈ u i := by
  simp only [flat, mem_join, Finset.mem_univ, true_and]








@[simp] theorem flat_row {J L : ℕ} (S : Finset (Coord J L)) : flat (row S) = S := by
  ext ⟨i, x⟩; simp


































theorem join_disjoint_compl {J L : ℕ} (I : Finset (Fin J))
    (u v : Fin J → Finset (Fin L)) : Disjoint (join I u) (join Iᶜ v) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, x⟩ hx hy
  exact (Finset.mem_compl.mp (mem_join.mp hy).1) (mem_join.mp hx).1

theorem join_subset {J L : ℕ} (I : Finset (Fin J)) {u v : Fin J → Finset (Fin L)}
    (h : ∀ i ∈ I, u i ⊆ v i) : join I u ⊆ join I v := by
  intro ⟨i, x⟩ hx
  obtain ⟨hi, hx⟩ := mem_join.mp hx
  exact mem_join.mpr ⟨hi, h i hi hx⟩

theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _

theorem join_card_of_balance {J L h : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (hu : ∀ i ∈ I, (u i).card = h) :
    (join I u).card = I.card * h := by
  rw [join_card]
  simp only [Finset.sum_congr rfl hu, Finset.sum_const, Nat.nsmul_eq_mul]

theorem flat_card_of_balance {J L h : ℕ} (u : Fin J → Finset (Fin L))
    (hu : ∀ i, (u i).card = h) : (flat u).card = J * h := by
  simpa only [flat, Finset.card_univ, Fintype.card_fin] using
    join_card_of_balance (Finset.univ : Finset (Fin J)) u (fun i _ => hu i)

theorem card_of_balanced_rows {J L h : ℕ} (S : Finset (Coord J L))
    (hS : ∀ i, (row S i).card = h) : S.card = J * h := by
  rw [← flat_row S]
  exact flat_card_of_balance _ hS






/-- Size arithmetic for the actual remaining Q blocks. The parameter I is
any set of completed blocks, including the initial segment used in reporting. -/
theorem forced_sizes {J L h : ℕ} (I : Finset (Fin J))
    (Q u : Fin J → Finset (Fin L)) (hQ : ∀ i, (Q i).card = 2 * h)
    (hu : ∀ i ∈ I, u i ⊆ Q i ∧ (u i).card = h) :
    (join Iᶜ Q).card =
      (J * h - (join I u).card) +
      (J * h - (join I (fun i => Q i \ u i)).card) := by
  have hU := join_card_of_balance I u (fun i hi => (hu i hi).2)
  have hV := join_card_of_balance (h := h) I (fun i => Q i \ u i) (fun i hi => by
    rw [Finset.card_sdiff_of_subset (hu i hi).1, hQ i, (hu i hi).2]
    omega)
  have hR := join_card_of_balance Iᶜ Q (fun i _ => hQ i)
  have hcompl : Iᶜ.card = J - I.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  rw [hU, hV, hR, hcompl, ← Nat.sub_mul]
  ring

end ThreeSum.BlockRows

end

section


/-!
# Independent trimmed endpoint histograms on the flattened block ground set

A histogram only inspects one endpoint and the occurrence vector. Its support
is exactly on independently retained balanced block subsets. Compatible
opposite endpoints reconstruct an actual retained choice tuple.
-/

namespace ThreeSum.BlockEncoding

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows











































































































































































section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]













theorem leftWeights_cardinality {h J : ℕ} (o : Occurrences h J) (P : ℤ)
    (B : Finset β) (b : β → ℤ) (S : Finset (Coord J (512 * h)))
    (hS : (leftWeights o P B b S : ℤ) ≠ 0) : S.card = J * h := by
  have ha : LeftAllowed o S := by
    by_contra hn
    exact hS (by simp only [leftWeights, hn, ite_false, Nat.cast_zero])
  exact card_of_balanced_rows S (fun i => (ha i).1)

theorem rightWeights_cardinality {h J : ℕ} (o : Occurrences h J) (P d : ℤ)
    (C : Finset γ) (c : γ → ℤ) (V : Finset (Coord J (512 * h)))
    (hV : (rightWeights o P d C c V : ℤ) ≠ 0) : V.card = J * h := by
  have ha : RightAllowed o V := by
    by_contra hn
    exact hV (by simp only [rightWeights, hn, ite_false, Nat.cast_zero])
  exact card_of_balanced_rows V (fun i => (ha i).1)













end Histograms

end ThreeSum.BlockEncoding

end

section


/-!
# Actual forced-prefix endpoint decompositions

Fixing completed blocks partitions each full retained tuple into its fixed
left/right subsets and its remaining left subset. The reconstruction is a
bijection, which identifies every prefix bucket sum with the subset formula.
-/

namespace ThreeSum.BlockForced

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding

section FiniteRows

variable {J L : ℕ}



































































































end FiniteRows



























































































section WeightedCounts

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
















































/-- This is the actual forced-prefix identity: all support, size and
reconstruction hypotheses are discharged by the concrete block encoding. -/
theorem transformPrefixValue_eq_bucket_sum_sourceProof {h J : ℕ} (P d : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h)))
    (hu : ∀ i ∈ I, u i ⊆ outputRows q i ∧ (u i).card = h) :
    transformPrefixValue P d B C b c q I u =
      (∑ t ∈ completedTuples q I u, leftBucket P B b t * rightBucket P d C c t : ℕ) := by
  have hQ : ∀ i, (outputRows q i).card = 2 * h :=
    fun i => LayerCounts.mem_vertices.mp (q i).2.property
  have he := Subset.forced_prefix_identity
    (fun S => (leftWeights (outputOccurrences q) P B b S : ℤ))
    (fun V => (rightWeights (outputOccurrences q) P d C c V : ℤ))
    (prefixLeft I u) (prefixRight I (outputRows q) u) (suffixDomain I)
    (remaining I (outputRows q)) (J * h) (J * h)
    (leftWeights_cardinality (outputOccurrences q) P B b)
    (rightWeights_cardinality (outputOccurrences q) P d C c)
    (join_disjoint_compl I u (fun _ => univ))
    (join_disjoint_compl I (fun i => outputRows q i \ u i) (fun _ => univ))
    (join_subset Iᶜ (fun _ _ => Finset.subset_univ _))
    (forced_sizes I (outputRows q) u hQ hu)
  rw [transformPrefixValue, he]
  exact_mod_cast (completed_bucket_sum P d B C b c q I u (fun i hi => (hu i hi).1)).symm

end WeightedCounts

end ThreeSum.BlockForced

end

universe u_1 u_2

theorem solution : ∀ {β : Type u_1} {γ : Type u_2} [Fintype.{u_1} β] [Fintype.{u_2} γ] [DecidableEq.{u_1 + 1} β] [DecidableEq.{u_2 + 1} γ]
  {h J : Nat} (P d : Int) (B : Finset.{u_1} β) (C : Finset.{u_2} γ) (b : β → Int) (c : γ → Int)
  (q : ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset.{0} (Fin J))
  (u :
    Fin J →
      Finset.{0}
        (Fin
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))),
  (∀ (i : Fin J),
      @Membership.mem.{0, 0} (Fin J) (Finset.{0} (Fin J))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin J)) (Fin J) (@Finset.instSetLike.{0} (Fin J))) I i →
        And
          (@LE.le.{0}
            (Finset.{0}
              (Fin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
            (@Preorder.toLE.{0}
              (Finset.{0}
                (Fin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
              (@PartialOrder.toPreorder.{0}
                (Finset.{0}
                  (Fin
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))
                (@Finset.instPartialOrder.{0}
                  (Fin
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h)))))
            (u i) (@ThreeSum.BlockForced.outputRows h J q i))
          (@Eq.{1} Nat
            (@Finset.card.{0}
              (Fin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))
              (u i))
            h)) →
    @Eq.{1} Int (@ThreeSum.BlockForced.transformPrefixValue.{u_1, u_2} β γ h J P d B C b c q I u)
      (@Nat.cast.{0} Int instNatCastInt
        (∑ t ∈ @ThreeSum.BlockForced.completedTuples h J q I u,
          @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@ThreeSum.RawIncidences.leftBucket.{u_1} β h J P B b t)
            (@ThreeSum.RawIncidences.rightBucket.{u_2} γ h J P d C c t))) := by
  exact @ThreeSum.BlockForced.transformPrefixValue_eq_bucket_sum_sourceProof

#print axioms solution
