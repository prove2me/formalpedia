-- Prove2me | solution 1 for SaturatedNet.Uniqueness.proposition_1_i
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:27:26.554045+00:00
-- url     : https://prove2.me/submissions/f3bf83dc-fff4-4835-8514-f200db1fcc60

import Mathlib
import Definitions.Def_SaturatedNet_Uniqueness_Model
open Matrix


namespace SaturatedNet.Uniqueness.LatticeProof

lemma complete_lattice_image {A B : Type*} [CompleteLattice A] [PartialOrder B]
    (e : A ↪o B) :
    (∀ S ⊆ Set.range e,
      (∃ u, IsLeast (upperBounds S ∩ Set.range e) u) ∧
      (∃ l, IsGreatest (lowerBounds S ∩ Set.range e) l)) ∧
    (∃ xmin, IsLeast (Set.range e) xmin) ∧
    (∃ xmax, IsGreatest (Set.range e) xmax) := by
  refine ⟨?_, ⟨e ⊥, ⟨⊥, rfl⟩, ?_⟩, ⟨e ⊤, ⟨⊤, rfl⟩, ?_⟩⟩
  · intro S hS
    constructor
    · refine ⟨e (sSup (e ⁻¹' S)), ⟨?_, ⟨_, rfl⟩⟩, ?_⟩
      · intro b hb
        obtain ⟨a, rfl⟩ := hS hb
        exact e.monotone (le_sSup hb)
      · rintro b ⟨hb, a, rfl⟩
        apply e.monotone
        apply sSup_le
        intro a' ha'
        exact e.le_iff_le.mp (hb ha')
    · refine ⟨e (sInf (e ⁻¹' S)), ⟨?_, ⟨_, rfl⟩⟩, ?_⟩
      · intro b hb
        obtain ⟨a, rfl⟩ := hS hb
        exact e.monotone (sInf_le hb)
      · rintro b ⟨hb, a, rfl⟩
        apply e.monotone
        apply le_sInf
        intro a' ha'
        exact e.le_iff_le.mp (hb ha')
  · rintro _ ⟨a, rfl⟩
    exact e.monotone bot_le
  · rintro _ ⟨a, rfl⟩
    exact e.monotone le_top

end SaturatedNet.Uniqueness.LatticeProof

open SaturatedNet.Uniqueness.LatticeProof

namespace SaturatedNet.Uniqueness

theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℝ) (hP : ∀ i j, 0 ≤ P i j) (w : n → ℝ) (hw : 0 ≤ w) (c : n → ℝ) :
    (∀ S ⊆ equilibria P w c,
      (∃ u, IsLeast (upperBounds S ∩ equilibria P w c) u) ∧
      (∃ l, IsGreatest (lowerBounds S ∩ equilibria P w c) l)) ∧
    (∃ xmin, IsLeast (equilibria P w c) xmin) ∧
    (∃ xmax, IsGreatest (equilibria P w c) xmax) := by
  let : ∀ i : n, Fact ((0 : ℝ) ≤ w i) := fun i => ⟨hw i⟩
  let B := ∀ i : n, Set.Icc (0 : ℝ) (w i)
  let val : B → (n → ℝ) := fun x i => (x i).val
  have hbound : ∀ i y, sat (w i) y ∈ Set.Icc (0 : ℝ) (w i) := by
    intro i y
    exact ⟨le_min (le_max_right _ _) (hw i), min_le_right _ _⟩
  let f : B →o B := {
    toFun := fun x i => ⟨sat (w i) (inflow P c (val x) i), hbound i _⟩
    monotone' := by
      intro x y hxy i
      change min (max (inflow P c (val x) i) 0) (w i) ≤
        min (max (inflow P c (val y) i) 0) (w i)
      apply min_le_min_right
      apply max_le_max_right
      exact add_le_add (Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_right (hxy j) (hP j i))) le_rfl }
  let : CompleteLattice (Function.fixedPoints f) := fixedPoints.completeLattice f
  let e : Function.fixedPoints f ↪o (n → ℝ) := {
    toFun := fun x => val x.val
    inj' := by
      intro x y h
      apply Subtype.ext
      funext i
      exact Subtype.ext (congrFun h i)
    map_rel_iff' := Iff.rfl }
  have he : Set.range e = equilibria P w c := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      intro i
      have h := congrArg (fun y : B => (y i : ℝ)) z.property
      exact h.symm
    · intro hx
      let z : B := fun i => ⟨x i, by rw [hx i]; exact hbound i _⟩
      have hz : f z = z := by
        funext i
        apply Subtype.ext
        exact (hx i).symm
      exact ⟨⟨z, hz⟩, rfl⟩
  simpa only [he] using complete_lattice_image e


end SaturatedNet.Uniqueness
