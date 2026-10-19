-- Prove2me | solution 1 for SoficGroups.lef_of_expanding_centralizer_models
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/9771aa5d-d38c-4636-82c6-a500fd67a41d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_exists_permutation_embedding_of_expanding_centralizer

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {G : Type*} [Group G]
    (hmodels : ∀ F : Finset G,
      Nonempty (ExpandingCentralizerFiniteModel G F)) : LEF G := by
  constructor
  intro F
  obtain ⟨M⟩ := hmodels F
  obtain ⟨n, f, hinj, hone, hmul⟩ :=
    exists_permutation_embedding_of_expanding_centralizer F M
  exact ⟨n, f, hinj, ⟨hone, hmul⟩⟩
end SoficGroups
