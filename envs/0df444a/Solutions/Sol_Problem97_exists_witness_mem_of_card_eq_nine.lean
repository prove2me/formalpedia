-- Prove2me | solution 1 for Problem97.exists_witness_mem_of_card_eq_nine
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-13T02:23:16.609242+00:00
-- url     : https://prove2.me/submissions/7cc7bf69-574e-4df5-bdec-b449f5e04a4c

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Author: Adam McKenna
-/

import Definitions.Def_Problem97_IsWitnessSystem
import Theorems.Thm_Problem97_K4_delete_of_indeg_zero
import Theorems.Thm_Erdos9796Mission_counterexample_card_ge_nine

open scoped EuclideanGeometry
open Finset
open Erdos9796Mission
open Problem97

/-!
# Nine-point witness incidence

This proof combines the witness-system deletion lemma with the published
nine-point counting lower bound. If a point had no incoming witness edge,
deleting it would leave an eight-point configuration, contradicting that
lower bound. The counting route follows Dumitrescu's method; the Lean proof
here is this project's formalization.
-/

theorem solution {A : Finset Plane} (hne : A.Nonempty)
    (hconv : Problem97.ConvexIndep A) (hK4 : Problem97.HasNEquidistantProperty 4 A)
    (hcard : A.card = 9) {S : Plane → Finset Plane}
    (hS : Problem97.IsWitnessSystem A S)
    {x : Plane} (hxA : x ∈ A) : ∃ y ∈ A, x ∈ S y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne', hconv', hK4'⟩ :=
    K4_delete_of_indeg_zero hne hconv hK4 hS hxA hcon
  have h9 : 9 ≤ (A.erase x).card :=
    Erdos9796Mission.counterexample_card_ge_nine (A.erase x) hne' hconv' hK4'
  have herase : (A.erase x).card = A.card - 1 := Finset.card_erase_of_mem hxA
  omega
