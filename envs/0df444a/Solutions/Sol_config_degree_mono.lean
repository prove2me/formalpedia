-- Prove2me | solution 1 for config_degree_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:46:26.511807+00:00
-- url     : https://prove2.me/submissions/2dab7de4-1cd9-43f4-878e-050d1fa91782

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
theorem _root_.solution {q : G.V} {c c' : Config G q} (h_le : c ≤ c') :
  config_degree c ≤ config_degree c' := by
  dsimp only [config_degree, deg, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  exact Finset.sum_le_sum fun v _ => h_le v
