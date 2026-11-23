-- Prove2me | solution 1 for burn_flow_directed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:49:19.229739+00:00
-- url     : https://prove2.me/submissions/e7748b3a-4dd0-4945-80f6-98323e6f5b04

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Definitions.Def_ChipFiringWithLean_Config
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_legal_set_empty
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty



set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph} {q : G.V} {c : Config G q} (L : burn_list G c) (h_full : ∀ v : G.V, v ∈ L.list) : ∀ (u v : G.V), burn_flow L ⟨u,v⟩ = 0 ∨ burn_flow L ⟨v,u⟩ = 0 := by
  intro u v
  dsimp only [burn_flow]
  by_cases h_uv : L.list.idxOf v < L.list.idxOf u
  . -- Case: indexOf v < indexOf u
    simp only [h_full u, h_uv, and_self, ↓reduceIte, h_full v, true_and, ite_eq_right_iff]
    right
    intro h
    linarith
  . -- Case: indexOf v ≥ indexOf u
    by_cases h_eq : L.list.idxOf u = L.list.idxOf v
    . -- Subcase: indexOf u = indexOf v
      simp only [h_eq, lt_self_iff_false, and_false, ↓reduceIte, or_self]
    . -- Subcase: indexOf u > indexOf v
      have h_uv' : L.list.idxOf u < L.list.idxOf v := by
        simp only [not_lt] at h_uv h_eq
        exact lt_of_le_of_ne h_uv h_eq
      simp only [h_uv, and_false, ↓reduceIte, h_full v, h_uv', and_self, true_or]
