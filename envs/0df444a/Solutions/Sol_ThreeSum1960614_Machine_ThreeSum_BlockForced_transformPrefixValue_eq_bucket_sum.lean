-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.BlockForced.transformPrefixValue_eq_bucket_sum
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:13:58.451567+00:00
-- url     : https://prove2.me/submissions/b08786f7-273e-4650-867c-ae9d5beb8509

import Aesop
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockForced_completed_bucket_sum
import Theorems.Thm_ThreeSum_Subset_forced_prefix_identity

namespace Finset
end Finset
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting

namespace ThreeSum1960614.Machine

/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows
open _root_.ThreeSum.BlockRows


open _root_.Finset
open scoped _root_.BigOperators









@[simp] theorem mem_join {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ _root_.ThreeSum.BlockRows.join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma

@[simp] theorem mem_flat {J L : ℕ} {u : Fin J → Finset (Fin L)}
    {i : Fin J} {x : Fin L} : Sigma.mk i x ∈ _root_.ThreeSum.BlockRows.flat u ↔ x ∈ u i := by
  simp only [_root_.ThreeSum.BlockRows.flat, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join, Finset.mem_univ, true_and]





@[simp] theorem flat_row {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) : _root_.ThreeSum.BlockRows.flat (_root_.ThreeSum.BlockRows.row S) = S := by
  ext ⟨i, x⟩; simp















theorem join_disjoint_compl {J L : ℕ} (I : Finset (Fin J))
    (u v : Fin J → Finset (Fin L)) : Disjoint (_root_.ThreeSum.BlockRows.join I u) (_root_.ThreeSum.BlockRows.join Iᶜ v) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, x⟩ hx hy
  exact (Finset.mem_compl.mp (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp hy).1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp hx).1

theorem join_subset {J L : ℕ} (I : Finset (Fin J)) {u v : Fin J → Finset (Fin L)}
    (h : ∀ i ∈ I, u i ⊆ v i) : _root_.ThreeSum.BlockRows.join I u ⊆ _root_.ThreeSum.BlockRows.join I v := by
  intro ⟨i, x⟩ hx
  obtain ⟨hi, hx⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp hx
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mpr ⟨hi, h i hi hx⟩

theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockRows.join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _

theorem join_card_of_balance {J L h : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (hu : ∀ i ∈ I, (u i).card = h) :
    (_root_.ThreeSum.BlockRows.join I u).card = I.card * h := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card]
  simp only [Finset.sum_congr rfl hu, Finset.sum_const, Nat.nsmul_eq_mul]

theorem flat_card_of_balance {J L h : ℕ} (u : Fin J → Finset (Fin L))
    (hu : ∀ i, (u i).card = h) : (_root_.ThreeSum.BlockRows.flat u).card = J * h := by
  simpa only [_root_.ThreeSum.BlockRows.flat, Finset.card_univ, Fintype.card_fin] using
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance (Finset.univ : Finset (Fin J)) u (fun i _ => hu i)

theorem card_of_balanced_rows {J L h : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L))
    (hS : ∀ i, (_root_.ThreeSum.BlockRows.row S i).card = h) : S.card = J * h := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.flat_row S]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.flat_card_of_balance _ hS





/-- Size arithmetic for the actual remaining Q blocks. The parameter I is
any set of completed blocks, including the initial segment used in reporting. -/
theorem forced_sizes {J L h : ℕ} (I : Finset (Fin J))
    (Q u : Fin J → Finset (Fin L)) (hQ : ∀ i, (Q i).card = 2 * h)
    (hu : ∀ i ∈ I, u i ⊆ Q i ∧ (u i).card = h) :
    (_root_.ThreeSum.BlockRows.join Iᶜ Q).card =
      (J * h - (_root_.ThreeSum.BlockRows.join I u).card) +
      (J * h - (_root_.ThreeSum.BlockRows.join I (fun i => Q i \ u i)).card) := by
  have hU := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance I u (fun i hi => (hu i hi).2)
  have hV := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance (h := h) I (fun i => Q i \ u i) (fun i hi => by
    rw [Finset.card_sdiff_of_subset (hu i hi).1, hQ i, (hu i hi).2]
    omega)
  have hR := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance Iᶜ Q (fun i _ => hQ i)
  have hcompl : Iᶜ.card = J - I.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  rw [hU, hV, hR, hcompl, ← Nat.sub_mul]
  ring

end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Independent trimmed endpoint histograms on the flattened block ground set

A histogram only inspects one endpoint and the occurrence vector. Its support
is exactly on independently retained balanced block subsets. Compatible
opposite endpoints reconstruct an actual retained choice tuple.
-/

namespace ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockEncoding


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows





























































section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]





theorem leftWeights_cardinality {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (P : ℤ)
    (B : Finset β) (b : β → ℤ) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h)))
    (hS : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights o P B b S : ℤ) ≠ 0) : S.card = J * h := by
  have ha : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.LeftAllowed o S := by
    by_contra hn
    exact hS (by simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights, hn, ite_false, Nat.cast_zero])
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.card_of_balanced_rows S (fun i => (ha i).1)

theorem rightWeights_cardinality {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (P d : ℤ)
    (C : Finset γ) (c : γ → ℤ) (V : Finset (_root_.ThreeSum.BlockRows.Coord J (464 * h)))
    (hV : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights o P d C c V : ℤ) ≠ 0) : V.card = J * h := by
  have ha : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed o V := by
    by_contra hn
    exact hV (by simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights, hn, ite_false, Nat.cast_zero])
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.card_of_balanced_rows V (fun i => (ha i).1)





end Histograms

end ThreeSum.BlockEncoding

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced

set_option maxRecDepth 8000
open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
section

/-- This is the actual forced-prefix identity: all support, size and
reconstruction hypotheses are discharged by the concrete block encoding. -/
theorem ThreeSum1960614.Machine.ThreeSum.BlockForced.transformPrefixValue_eq_bucket_sum__implementation_4bbfdae96c {h J : ℕ} (P d : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (464 * h)))
    (hu : ∀ i ∈ I, u i ⊆ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q i ∧ (u i).card = h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.transformPrefixValue P d B C b c q I u =
      (∑ t ∈ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q I u, _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.leftBucket P B b t * _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rightBucket P d C c t : ℕ) := by
  have hQ : ∀ i, (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q i).card = 2 * h :=
    fun i => _root_.ThreeSum.LayerCounts.mem_vertices.mp (q i).2.property
  have he := _root_.ThreeSum.Subset.forced_prefix_identity
    (fun S => (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P B b S : ℤ))
    (fun V => (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P d C c V : ℤ))
    (_root_.ThreeSum.BlockForced.prefixLeft I u) (_root_.ThreeSum.BlockForced.prefixRight I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u) (_root_.ThreeSum.BlockForced.suffixDomain I)
    (_root_.ThreeSum.BlockForced.remaining I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)) (J * h) (J * h)
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights_cardinality (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P B b)
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights_cardinality (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P d C c)
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_disjoint_compl I u (fun _ => univ))
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_disjoint_compl I (fun i => _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q i \ u i) (fun _ => univ))
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_subset Iᶜ (fun _ _ => Finset.subset_univ _))
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.forced_sizes I (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) u hQ hu)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.transformPrefixValue, he]
  exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completed_bucket_sum P d B C b c q I u (fun i hi => (hu i hi).1)).symm
end

end

theorem solution.{u_implementation_0,u_implementation_1} : type_of% (@ThreeSum1960614.Machine.ThreeSum.BlockForced.transformPrefixValue_eq_bucket_sum__implementation_4bbfdae96c.{u_implementation_0,u_implementation_1}) := (@ThreeSum1960614.Machine.ThreeSum.BlockForced.transformPrefixValue_eq_bucket_sum__implementation_4bbfdae96c.{u_implementation_0,u_implementation_1})

#print axioms solution
