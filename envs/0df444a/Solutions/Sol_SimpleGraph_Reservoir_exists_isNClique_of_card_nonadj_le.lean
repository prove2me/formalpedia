-- Prove2me | solution 1 for SimpleGraph.Reservoir.exists_isNClique_of_card_nonadj_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:31:49.435092+00:00
-- url     : https://prove2.me/submissions/a8f44145-7f00-4693-b31d-15267599d4cf

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_spine
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Reservoir_exists_isNClique_succ
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_spine
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_pool
public import Theorems.Thm_SimpleGraph_Reservoir_card_pivot_spine
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_pool_subset
public import Theorems.Thm_SimpleGraph_Reservoir_card_pivot_pool
attribute [local simp] SimpleGraph.Reservoir.ofPool_spine
attribute [local simp] SimpleGraph.Reservoir.ofPool_pool
attribute [local simp] SimpleGraph.Reservoir.pivot_spine
attribute [local simp] SimpleGraph.Reservoir.pivot_pool

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Reservoir
variable {G}
variable (R : G.Reservoir)
namespace SimpleGraph.Reservoir
theorem _root_.solution [DecidableRel G.Adj] {d : ℕ}
    (hd : ∀ v ∈ R.pool, #{w ∈ R.pool | ¬G.Adj v w} ≤ d) (j : ℕ) (hj : j * d < #R.pool) :
    ∃ s, G.IsNClique (#R.spine + (j + 1)) s := by
  classical
  induction j generalizing R with
  | zero =>
    exact R.exists_isNClique_succ (card_pos.mp (by simpa using hj))
  | succ j ih =>
    obtain ⟨v, hv⟩ := card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hj)
    have hloss := R.card_pivot_pool hv
    have hv' := hd v hv
    have hsub := R.pivot_pool_subset hv
    have hd' : ∀ w ∈ (R.pivot v hv).pool,
        #{u ∈ (R.pivot v hv).pool | ¬G.Adj w u} ≤ d := fun w hw =>
      (card_le_card (filter_subset_filter _ hsub)).trans (hd w (hsub hw))
    have hj' : j * d < #(R.pivot v hv).pool := by
      rw [Nat.succ_mul] at hj
      generalize j * d = m at hj ⊢
      omega
    obtain ⟨s, hs⟩ := ih (R.pivot v hv) hd' hj'
    rw [card_pivot_spine] at hs
    exact ⟨s, by rwa [show #R.spine + (j + 1 + 1) = #R.spine + 1 + (j + 1) by omega]⟩
end SimpleGraph.Reservoir
