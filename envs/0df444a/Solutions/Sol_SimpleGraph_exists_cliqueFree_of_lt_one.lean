-- Prove2me | solution 1 for SimpleGraph.exists_cliqueFree_of_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:33.90272+00:00
-- url     : https://prove2.me/submissions/ec7ae353-0663-464b-9865-b54b7d8f5944

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Theorems.Thm_SimpleGraph_isClique_fromEdgeSet_iff
public import Theorems.Thm_SimpleGraph_isClique_compl_fromEdgeSet_iff
public import Theorems.Thm_SimpleGraph_bernoulliProb_isClique
public import Theorems.Thm_SimpleGraph_bernoulliProb_isClique_compl
public import Theorems.Thm_Finset_exists_le_expectation
public import Theorems.Thm_Finset_expectation_card_filter

section
@[expose] public section
open Finset
namespace Finset
variable {V : Type*} [DecidableEq V]
end Finset
namespace SimpleGraph
variable {V : Type*} [DecidableEq V]
variable [Fintype V] {p : ℝ}
private theorem expectation_bad (k l : ℕ) :
    ∑ A ∈ (possibleEdges V).powerset, (possibleEdges V).bernoulliWeight p A *
        ((#{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} : ℝ) +
          #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs}) =
      (Fintype.card V).choose k * p ^ k.choose 2 +
        (Fintype.card V).choose l * (1 - p) ^ l.choose 2 := by
  simp_rw [mul_add, sum_add_distrib]
  have x1 := expectation_card_filter (U := possibleEdges V) (p := p)
    ((univ : Finset V).powersetCard k) (fun s A => s.pairs ⊆ A)
  have x2 := expectation_card_filter (U := possibleEdges V) (p := p)
    ((univ : Finset V).powersetCard l) (fun s A => Disjoint A s.pairs)
  rw [x1, x2]
  have e1 : ∀ s ∈ (univ : Finset V).powersetCard k,
      (possibleEdges V).bernoulliProb p (s.pairs ⊆ ·) = p ^ k.choose 2 := fun s hs => by
    rw [bernoulliProb_isClique, (mem_powersetCard.mp hs).2]
  have e2 : ∀ s ∈ (univ : Finset V).powersetCard l,
      (possibleEdges V).bernoulliProb p (Disjoint · s.pairs) = (1 - p) ^ l.choose 2 :=
    fun s hs => by
    rw [bernoulliProb_isClique_compl, (mem_powersetCard.mp hs).2]
  rw [sum_congr rfl e1, sum_congr rfl e2, sum_const, sum_const, card_powersetCard,
    card_powersetCard, card_univ, nsmul_eq_mul, nsmul_eq_mul]
end SimpleGraph
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [DecidableEq V]
variable [Fintype V] {p : ℝ}
omit [DecidableEq V]
namespace SimpleGraph
theorem _root_.solution (h0 : 0 ≤ p) (h1 : p ≤ 1) {k l : ℕ}
    (h : (Fintype.card V).choose k * p ^ k.choose 2 +
      (Fintype.card V).choose l * (1 - p) ^ l.choose 2 < 1) :
    ∃ G : SimpleGraph V, G.CliqueFree k ∧ Gᶜ.CliqueFree l := by
  classical
  obtain ⟨A, -, hA⟩ := exists_le_expectation h0 h1 fun A =>
    ((#{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} : ℝ) +
      #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs})
  rw [expectation_bad] at hA
  have hzero : #{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} = 0 ∧
      #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs} = 0 := by
    have : ((#{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} +
        #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs} : ℕ) : ℝ) < 1 := by
      push_cast; linarith
    have : #{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} +
        #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs} = 0 := by
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    omega
  refine ⟨fromEdgeSet (A : Set (Sym2 V)), fun s hs => ?_, fun s hs => ?_⟩
  · exact (card_eq_zero.mp hzero.1 ▸ mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,
      hs.card_eq⟩, isClique_fromEdgeSet_iff.mp hs.isClique⟩ : s ∈ (∅ : Finset (Finset V))) |>
      Finset.notMem_empty s
  · exact (card_eq_zero.mp hzero.2 ▸ mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,
      hs.card_eq⟩, (isClique_compl_fromEdgeSet_iff.mp hs.isClique).symm⟩ :
      s ∈ (∅ : Finset (Finset V))) |>
      Finset.notMem_empty s
end SimpleGraph
