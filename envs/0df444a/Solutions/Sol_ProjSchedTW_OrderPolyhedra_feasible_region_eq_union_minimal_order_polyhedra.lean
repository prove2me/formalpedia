-- Prove2me | solution 1 for ProjSchedTW.OrderPolyhedra.feasible_region_eq_union_minimal_order_polyhedra
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T20:15:07.737866+00:00
-- url     : https://prove2.me/submissions/0cb5de46-dc67-4003-959c-fde549e5b10b

import Mathlib
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Project
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Resources
import Definitions.Def_ProjSchedTW_OrderPolyhedra_Orders
import Theorems.Thm_ProjSchedTW_OrderPolyhedra_schedule_order_feasible_iff

open ProjSchedTW.OrderPolyhedra

private lemma exists_minimal_feasibleOrder_subset {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) {O₀ : Finset (Fin (n + 2) × Fin (n + 2))} (hO₀ : P.IsFeasibleOrder O₀) :
    ∃ O ⊆ O₀, Minimal P.IsFeasibleOrder O := by
  induction O₀ using Finset.strongInduction with
  | H A ih =>
    by_cases hsub : ∃ B ⊂ A, P.IsFeasibleOrder B
    · rcases hsub with ⟨B, hBA, hB⟩
      rcases ih B hBA hB with ⟨O, hOB, hOmin⟩
      exact ⟨O, Finset.Subset.trans hOB hBA.subset, hOmin⟩
    · refine ⟨A, Finset.Subset.rfl, ⟨hO₀, fun B hB hBA => ?_⟩⟩
      by_contra hnot
      exact hsub ⟨B, lt_of_le_not_ge hBA hnot, hB⟩

theorem solution {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions) :
    {O : Finset (Fin (n + 2) × Fin (n + 2)) | Minimal P.IsFeasibleOrder O}.Finite ∧
    {S : Fin (n + 2) → ℝ | P.IsFeasible S} =
      ⋃ O ∈ {O : Finset (Fin (n + 2) × Fin (n + 2)) | Minimal P.IsFeasibleOrder O},
        P.orderPolyhedron O := by
  refine ⟨Set.toFinite _, Set.ext fun S => ⟨?_, ?_⟩⟩
  · intro hS
    have hO₀ : P.IsFeasibleOrder (P.scheduleOrder S) :=
      (schedule_order_feasible_iff P hP S hS.1).mpr hS
    obtain ⟨O, hOsub, hOmin⟩ := exists_minimal_feasibleOrder_subset P hO₀
    rw [Set.mem_iUnion₂]
    refine ⟨O, hOmin, hS.1, fun e heO => ?_⟩
    have heS : e ∈ P.scheduleOrder S := hOsub heO
    unfold Project.scheduleOrder at heS
    rw [Finset.mem_filter] at heS
    exact heS.2.2
  · intro hS
    rw [Set.mem_iUnion₂] at hS
    rcases hS with ⟨O, hOmin, hSO⟩
    exact hOmin.prop.2 S hSO
