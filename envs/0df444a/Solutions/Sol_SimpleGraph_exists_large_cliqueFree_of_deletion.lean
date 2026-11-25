-- Prove2me | solution 1 for SimpleGraph.exists_large_cliqueFree_of_deletion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:35.841807+00:00
-- url     : https://prove2.me/submissions/3cf7646d-ec91-4473-925a-a7976160e361

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
theorem _root_.solution (h0 : 0 ≤ p) (h1 : p ≤ 1) {k l : ℕ} (hk : 1 ≤ k)
    (hl : 1 ≤ l) :
    ∃ (G : SimpleGraph V) (t : Finset V),
      (Fintype.card V : ℝ) - ((Fintype.card V).choose k * p ^ k.choose 2 +
        (Fintype.card V).choose l * (1 - p) ^ l.choose 2) ≤ #t ∧
      (∀ s ⊆ t, ¬G.IsNClique k s) ∧ ∀ s ⊆ t, ¬Gᶜ.IsNClique l s := by
  classical
  obtain ⟨A, -, hA⟩ := exists_le_expectation h0 h1 fun A =>
    ((#{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} : ℝ) +
      #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs})
  rw [expectation_bad] at hA
  set G := fromEdgeSet (A : Set (Sym2 V))
  set B := ({s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} ∪
    {s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs})
  -- every bad set is nonempty; delete one vertex from each
  have hne : ∀ s ∈ B, s.Nonempty := by
    intro s hs
    rcases mem_union.mp hs with hs | hs <;> rw [mem_filter, mem_powersetCard] at hs <;>
      exact card_pos.mp (by omega)
  let H : Finset V := B.attach.image fun s => (hne s.1 s.2).choose
  refine ⟨G, univ \ H, ?_, ?_, ?_⟩
  · have hH : (#H : ℝ) ≤ #B := by exact_mod_cast card_image_le.trans (card_attach).le
    have hB : (#B : ℝ) ≤ (#{s ∈ (univ : Finset V).powersetCard k | s.pairs ⊆ A} : ℝ) +
        #{s ∈ (univ : Finset V).powersetCard l | Disjoint A s.pairs} := by
      exact_mod_cast card_union_le _ _
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Nat.cast_sub (card_le_univ _)]
    linarith
  · intro s hs hcl
    have hsB : s ∈ B := mem_union_left _ (mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,
      hcl.card_eq⟩, isClique_fromEdgeSet_iff.mp hcl.isClique⟩)
    have hmem := (hne s hsB).choose_spec
    exact (mem_sdiff.mp (hs hmem)).2 (mem_image.mpr ⟨⟨s, hsB⟩, mem_attach _ _, rfl⟩)
  · intro s hs hcl
    have hsB : s ∈ B := mem_union_right _ (mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,
      hcl.card_eq⟩, (isClique_compl_fromEdgeSet_iff.mp hcl.isClique).symm⟩)
    have hmem := (hne s hsB).choose_spec
    exact (mem_sdiff.mp (hs hmem)).2 (mem_image.mpr ⟨⟨s, hsB⟩, mem_attach _ _, rfl⟩)
end SimpleGraph
