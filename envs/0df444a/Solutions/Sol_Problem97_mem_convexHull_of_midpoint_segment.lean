-- Prove2me | solution 1 for Problem97.mem_convexHull_of_midpoint_segment
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:12.112295+00:00
-- url     : https://prove2.me/submissions/f4471b64-f55f-4217-8045-264270c485d5

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.ConvexIndepHelpers:3069:4393. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation

section Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexIndepHelpers

open Problem97

/- Fragment from Erdos9796Proof.P97.ConvexIndepHelpers; source SHA-256 58fea6fdfc458ff582e9e12c324d10b6e51a5653a6daa5dc80f586642be49129 -/


/-!
# `ConvexIndep` Finset helpers (Milestone 2)

Direct proofs from the extreme-point characterization
`EuclideanGeometry.ConvexIndep S ↔ ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})`:

* `ConvexIndep.mono` — `B ⊆ A → ConvexIndep A → ConvexIndep B`
* `ConvexIndep.erase` — `ConvexIndep A → ConvexIndep (A.erase x)`

These power the M4 descent step: erasing a removable vertex from a
counterexample preserves convex independence, and more generally any
subset of a convex-independent set is convex independent.
-/

open scoped EuclideanGeometry














theorem solution {x y a b : ℝ²}
    (h : a ∈ segment ℝ (midpoint ℝ x y) b) :
    a ∈ convexHull ℝ ({x, y, b} : Set ℝ²) := by
  have hmid : midpoint ℝ x y ∈ convexHull ℝ ({x, y, b} : Set ℝ²) := by
    exact (segment_subset_convexHull (x := x) (y := y)
      (s := ({x, y, b} : Set ℝ²)) (by simp) (by simp))
      (midpoint_mem_segment x y)
  have hb : b ∈ convexHull ℝ ({x, y, b} : Set ℝ²) := by
    exact subset_convexHull _ _ (by simp)
  have hmb : a ∈ convexHull ℝ ({midpoint ℝ x y, b} : Set ℝ²) := by
    rw [convexHull_pair]
    exact h
  have hsub : ({midpoint ℝ x y, b} : Set ℝ²) ⊆
      convexHull ℝ ({x, y, b} : Set ℝ²) := by
    intro p hp
    rcases hp with rfl | rfl
    · exact hmid
    · exact hb
  have hmono : a ∈ convexHull ℝ (convexHull ℝ ({x, y, b} : Set ℝ²)) :=
    convexHull_mono hsub hmb
  have hfix : convexHull ℝ (convexHull ℝ ({x, y, b} : Set ℝ²)) =
      convexHull ℝ ({x, y, b} : Set ℝ²) := by
    exact convexHull_eq_self.mpr (convex_convexHull _ _)
  simpa [hfix] using hmono

end Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexIndepHelpers
