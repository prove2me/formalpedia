-- Prove2me | solution 1 for SimpleGraph.exists_dependentRandomChoice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:02:20.666379+00:00
-- url     : https://prove2.me/submissions/a28d5908-83dd-4d9a-a9ad-71b014e3a2fc

module
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Rify
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_DependentRandomChoice
public import Theorems.Thm_SimpleGraph_sum_card_commonNeighbors_tuple
public import Theorems.Thm_SimpleGraph_sum_card_bad_le

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution [Nonempty V] {t r m a : ℕ} (hr : 1 ≤ r)
    (h : a * Fintype.card V ^ t + (Fintype.card V).choose r * m ^ t ≤ ∑ v, G.degree v ^ t) :
    ∃ W : Finset V, a ≤ #W ∧ ∀ S ⊆ W, #S = r → m ≤ #{u | ∀ v ∈ S, G.Adj v u} := by
  set bad : (Fin t → V) → Finset (Finset V) := fun τ =>
    {S ∈ (univ : Finset V).powersetCard r |
      #{u | ∀ v ∈ S, G.Adj v u} < m ∧ ∀ i, ∀ v ∈ S, G.Adj (τ i) v}
  set W₀ : (Fin t → V) → Finset V := fun τ => {v | ∀ i, G.Adj (τ i) v}
  -- some tuple has `a + #bad ≤ |W₀|`
  have hsum : ∑ τ : Fin t → V, (a + #(bad τ)) ≤ ∑ τ : Fin t → V, #(W₀ τ) := by
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul,
      sum_card_commonNeighbors_tuple]
    have hb : ∑ τ : Fin t → V, #(bad τ) ≤ (Fintype.card V).choose r * m ^ t :=
      sum_card_bad_le G t r m
    rw [mul_comm]
    omega
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin t → V, a + #(bad τ) ≤ #(W₀ τ) := by
    by_contra! hlt
    exact (sum_lt_sum_of_nonempty univ_nonempty fun τ _ => hlt τ).not_ge hsum
  -- delete one vertex from each bad set
  have hne : ∀ S ∈ bad τ, S.Nonempty := fun S hS => by
    rw [mem_filter, mem_powersetCard] at hS
    exact card_pos.mp (by omega)
  set H : Finset V := (bad τ).attach.image fun S => (hne S.1 S.2).choose
  refine ⟨W₀ τ \ H, ?_, fun S hS hSr => ?_⟩
  · have hH : #H ≤ #(bad τ) := card_image_le.trans card_attach.le
    have := le_card_sdiff H (W₀ τ)
    omega
  · by_contra! hlt
    have hSW : ∀ i, ∀ v ∈ S, G.Adj (τ i) v := fun i v hv =>
      (mem_filter.mp (mem_sdiff.mp (hS hv)).1).2 i
    have hSbad : S ∈ bad τ := mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, hSr⟩, hlt, hSW⟩
    have hmem := (hne S hSbad).choose_spec
    exact (mem_sdiff.mp (hS hmem)).2 (mem_image.mpr ⟨⟨S, hSbad⟩, mem_attach _ _, rfl⟩)
end SimpleGraph
