-- Prove2me | solution 1 for Scott1972.ContinuousLattice.wayBelow_le_finset_sup_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:38:46.032248+00:00
-- url     : https://prove2.me/submissions/f71ef703-19e9-435f-8b28-29dd6717f8b5

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
import Theorems.Thm_Scott1972_ContinuousLattice_stepMap_apply_of_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_stepMap_le_of_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_stepMap_pointwise_sSup
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_sup
import Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_sSup_iff


set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
namespace Scott1972.ContinuousLattice
theorem _root_.solution (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D')
    {φ g : ScottMap D D'} (h : φ ≪ g) :
    ∃ F : Finset (D × D'), (∀ p ∈ F, (p.2 : D') ≪ (g : D → D') p.1) ∧
      φ ≤ F.sup (fun p => stepMap p.1 p.2) := by
  classical
  set Sg : Set (ScottMap D D') :=
    (fun F : Finset (D × D') => F.sup (fun p => stepMap p.1 p.2)) ''
      {F | ∀ p ∈ F, (p.2 : D') ≪ (g : D → D') p.1} with hSg
  have hSgne : Sg.Nonempty := by
    refine ⟨_, ∅, ?_, rfl⟩
    intro p hp
    exact absurd hp (Finset.notMem_empty p)
  have hSgdir : DirectedOn (· ≤ ·) Sg := by
    rintro _ ⟨F₁, hF₁, rfl⟩ _ ⟨F₂, hF₂, rfl⟩
    refine ⟨(F₁ ∪ F₂).sup (fun p => stepMap p.1 p.2), ⟨F₁ ∪ F₂, fun p hp => ?_, rfl⟩,
      Finset.sup_mono Finset.subset_union_left, Finset.sup_mono Finset.subset_union_right⟩
    rcases Finset.mem_union.1 hp with hp | hp
    · exact hF₁ p hp
    · exact hF₂ p hp
  have hSgsup : sSup Sg = g := by
    apply le_antisymm
    · refine sSup_le ?_
      rintro _ ⟨F, hF, rfl⟩
      exact Finset.sup_le fun p hp => stepMap_le_of_wayBelow (hF p hp)
    · rw [ScottMap.le_def]
      intro x
      rw [← stepMap_pointwise_sSup hD hD' g x]
      refine sSup_le ?_
      rintro e' ⟨e, hex, he'⟩
      have hmemSg : stepMap e e' ∈ Sg := by
        refine ⟨{(e, e')}, fun p hp => ?_, ?_⟩
        · rw [Finset.mem_singleton] at hp; subst hp; exact he'
        · show ({(e, e')} : Finset (D × D')).sup (fun p => stepMap p.1 p.2) = stepMap e e'
          rw [Finset.sup_singleton]
      have hx : (stepMap e e' : D → D') x ≤ ((sSup Sg : ScottMap D D') : D → D') x := by
        rw [ScottMap.sSup_apply]
        exact le_sSup ⟨stepMap e e', hmemSg, rfl⟩
      rwa [stepMap_apply_of_wayBelow hex] at hx
  rw [← hSgsup] at h
  obtain ⟨_, ⟨F, hF, rfl⟩, hφs⟩ := (wayBelow_sSup_iff hSgne hSgdir).1 h
  exact ⟨F, hF, hφs.le⟩
end Scott1972.ContinuousLattice
