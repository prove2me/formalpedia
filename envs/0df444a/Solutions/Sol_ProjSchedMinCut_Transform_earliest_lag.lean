-- Prove2me | solution 1 for ProjSchedMinCut.Transform.earliest_lag
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:12:30.480177+00:00
-- url     : https://prove2.me/submissions/b6aa0b0e-e91c-442a-8613-6539cb5b33fa

import Mathlib
import Definitions.Def_ProjSchedMinCut_Transform_Setting

open ProjSchedMinCut.Transform
open Instance in
theorem solution {n : ℕ} (I : Instance n) (hw : ∀ j t, 0 ≤ I.w j t)
    (hfeas : ∃ S, I.Feasible S) :
    ∀ ij ∈ I.L, I.earliest ij.1 + I.d ij.1 ij.2 ≤ I.earliest ij.2 := by
  intro ij hij
  obtain ⟨S0, hS0⟩ := hfeas
  have hbdd : ∀ j, BddBelow (I.startTimes j) := by
    intro j
    refine ⟨0, ?_⟩
    rintro t ⟨S, hS, rfl⟩
    exact (hS.2 j).1
  have hne : ∀ j, (I.startTimes j).Nonempty := fun j => ⟨S0 j, S0, hS0, rfl⟩
  have hmem := Int.csInf_mem (hne ij.2) (hbdd ij.2)
  obtain ⟨S, hS, hSj⟩ := hmem
  have hle : I.earliest ij.1 ≤ S ij.1 := csInf_le (hbdd ij.1) ⟨S, hS, rfl⟩
  have hlag := hS.1 ij hij
  have : I.earliest ij.2 = S ij.2 := by unfold Instance.earliest; exact hSj.symm
  rw [this]
  linarith
