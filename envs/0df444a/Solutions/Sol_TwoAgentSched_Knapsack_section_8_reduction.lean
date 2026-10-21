-- Prove2me | solution 1 for TwoAgentSched.Knapsack.section_8_reduction
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:07:39.753903+00:00
-- url     : https://prove2.me/submissions/c69357a8-e7d4-45ed-99ec-baac8707f421

import Mathlib
import Definitions.Def_TwoAgentSched_Knapsack_Model

set_option autoImplicit false
open TwoAgentSched.Knapsack

theorem solution (I : Instance) (QA Q : ℝ) (l : List (Fin I.nA ⊕ Fin I.nB)) :
    I.MeetsU QA (fun _ => Q) 0 l ↔ I.Meets QA Q l := by
  unfold Instance.MeetsU Instance.Meets Instance.numLateB
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun k => ?_⟩
    have h3' := Nat.le_zero.1 h3
    classical
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h3'
    exact not_lt.1 (h3' (Finset.mem_univ k))
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    classical
    refine Nat.le_zero.2 ?_
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k _
    exact not_lt.2 (h3 k)
