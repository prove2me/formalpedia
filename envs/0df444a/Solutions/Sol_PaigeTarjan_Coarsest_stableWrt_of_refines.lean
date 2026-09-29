-- Prove2me | solution 1 for PaigeTarjan.Coarsest.stableWrt_of_refines
-- status  : ACCEPTED   (prove)
-- author  : @37720879
-- created : 2026-09-28T04:28:36.005798+00:00
-- url     : https://prove2.me/submissions/d3b12e87-734e-4ec0-8a3e-2d5adb8814a4

import Definitions.Def_PaigeTarjan_Coarsest_Basic

/-
Source: Paige and Tarjan, Three Partition Refinement Algorithms (1987),
p. 978, property (1). https://doi.org/10.1137/0216062
Target: https://prove2.me/theorems/cd8b0277-0ef0-4666-ac35-389619f30b6b
Prepared with AI assistance; checked against the platform's original definitions.
-/

open PaigeTarjan.Coarsest

theorem solution {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (P R : Finset (Finset U)) (S : Finset U)
    (hP : IsPartition P) (hR : IsPartition R) (hRP : Refines R P)
    (hPS : StableWrt E P S) :
    StableWrt E R S := by
  intro B hB
  obtain ⟨C, hC, hBC⟩ := hRP B hB
  rcases hPS C hC with hCsub | hCdis
  · exact Or.inl (Finset.Subset.trans hBC hCsub)
  · exact Or.inr (hCdis.mono_left hBC)
