-- Prove2me | solution 1 for config_eff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:46:24.778626+00:00
-- url     : https://prove2.me/submissions/66f1161d-de86-4f73-8427-8f52514e00f0

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
theorem _root_.solution {q : G.V} (d : ℤ) (c : Config G q) : effective (toDiv d c) ↔ d ≥ config_degree c := by
  constructor
  -- Effective implies d ≥ config_degree
  intro h_eff
  have h := h_eff q
  rw [eval_toDiv_q] at h
  linarith
  -- d ≥ config_degree implies effective
  intro h_deg v
  by_cases h_v : v = q
  · -- Case v = q
    simp only [h_v, eval_toDiv_q, Int.sub_nonneg, h_deg]
  · -- Case v ≠ q
    simp only [ne_eq, h_v, not_false_eq_true, eval_toDiv_ne_q, ge_iff_le]
    exact c.non_negative v
