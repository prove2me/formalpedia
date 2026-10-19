-- Prove2me | solution 1 for SoficGroups.exists_local_word_control
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/5d3d74aa-b406-456e-9dc8-c6922961f947

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_LocalMultiplicativeOn_map_inv_of_mem

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {α : Type u} {G : Type v} [Group G]
    (φ : FreeGroup α →* G) (z : FreeGroup α) :
    ∃ s : Finset G, ∀ (H : Type w) [Group H] (f : G → H),
      LocalMultiplicativeOn s f →
        FreeGroup.lift (fun a => f (φ (FreeGroup.of a))) z = f (φ z) := by
  classical
  refine FreeGroup.induction_on z ?_ ?_ ?_ ?_
  · refine ⟨∅, ?_⟩
    intro H _ f hf
    simp [hf.map_one]
  · intro a
    refine ⟨∅, ?_⟩
    intro H _ f _
    simp
  · intro a _
    refine ⟨{φ (FreeGroup.of a), (φ (FreeGroup.of a))⁻¹}, ?_⟩
    intro H _ f hf
    simp only [map_inv, FreeGroup.lift_apply_of]
    exact (hf.map_inv_of_mem (by simp) (by simp)).symm
  · intro x y hx hy
    obtain ⟨sx, hx⟩ := hx
    obtain ⟨sy, hy⟩ := hy
    refine ⟨insert (φ x) (insert (φ y) (sx ∪ sy)), ?_⟩
    intro H _ f hf
    have hsx : sx ⊆ insert (φ x) (insert (φ y) (sx ∪ sy)) := by
      intro a ha
      simp [ha]
    have hsy : sy ⊆ insert (φ x) (insert (φ y) (sx ∪ sy)) := by
      intro a ha
      simp [ha]
    calc
      FreeGroup.lift (fun a => f (φ (FreeGroup.of a))) (x * y) =
          FreeGroup.lift (fun a => f (φ (FreeGroup.of a))) x *
            FreeGroup.lift (fun a => f (φ (FreeGroup.of a))) y := map_mul _ _ _
      _ = f (φ x) * f (φ y) :=
        congrArg₂ (· * ·) (hx H f (hf.mono hsx)) (hy H f (hf.mono hsy))
      _ = f (φ x * φ y) :=
        (hf.map_mul (φ x) (by simp) (φ y) (by simp)).symm
      _ = f (φ (x * y)) := by rw [map_mul]
end SoficGroups
