-- Prove2me | solution 1 for SizeRamsey.tau4_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:30:16.765069+00:00
-- url     : https://prove2.me/submissions/db37f3ba-98c7-4c05-a59e-a09f4a3fb75c

module
public import Definitions.Def_SizeRamsey_Shared
public import Definitions.Def_SizeRamsey_Basic
public import Theorems.Thm_SizeRamsey_tau4_le_card
public import Theorems.Thm_SizeRamsey_exists_transversal_card_eq_tau4

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey
namespace SizeRamsey
theorem _root_.solution
    {V : Type*} [Fintype V]
    {G H : SimpleGraph V} (h : G ≤ H) :
    tau4 G ≤ tau4 H := by
  obtain ⟨S, hS, hcard⟩ := exists_transversal_card_eq_tau4 H
  refine hcard ▸ tau4_le_card fun f hf => hS f ?_
  obtain ⟨hinj, h01, h12, h23, h30⟩ := hf
  exact ⟨hinj, h h01, h h12, h h23, h h30⟩
end SizeRamsey
