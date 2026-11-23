-- Prove2me | solution 1 for config_eq_of_le_and_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:23.589941+00:00
-- url     : https://prove2.me/submissions/ef148d9d-1b21-4360-9eaa-455a3276c50f

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
theorem _root_.solution {q : G.V} {c1 c2 : Config G q} (h_le : c2 ≤ c1)
    (h_deg : config_degree c1 = config_degree c2) : c1 = c2 := by
  apply (eq_config_iff_eq_chips c1 c2).mpr
  dsimp only [config_degree, deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h_deg
  have h_le' : ∀ v : G.V, c2.chips v ≤ c1.chips v := by
    intro v
    exact h_le v
  suffices ∀ v : G.V, c1.chips v = c2.chips v by
    funext v
    exact this v
  contrapose! h_deg with h_ne
  rcases h_ne with ⟨v, h_v_ne⟩
  have h_gt : c2.chips v < c1.chips v := by
    specialize h_le' v
    apply lt_of_le_of_ne h_le'
    contrapose! h_v_ne
    simp only [h_v_ne]
  suffices config_degree c2 < config_degree c1 by
    exact ne_of_gt this
  dsimp only [config_degree, deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  refine Finset.sum_lt_sum ?_ ?_
  · intro i _
    exact h_le' i
  · use v
    simp only [mem_univ, h_gt, and_self]
