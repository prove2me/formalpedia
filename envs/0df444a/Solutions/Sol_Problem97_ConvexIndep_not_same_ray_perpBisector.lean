-- Prove2me | solution 1 for Problem97.ConvexIndep.not_same_ray_perpBisector
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:45.874222+00:00
-- url     : https://prove2.me/submissions/f09b380a-c63f-4f13-9be0-748ab44b7093

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.ConvexIndepHelpers:4395:5402. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Theorems.Thm_Problem97_mem_convexHull_of_midpoint_segment

section Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexIndepHelpers

open Problem97 Problem97.ConvexIndep

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
















theorem solution {A : Finset ℝ²}
    (hA : ConvexIndep A) {x y a b : ℝ²}
    (hx : x ∈ A) (hy : y ∈ A) (ha : a ∈ A) (hb : b ∈ A)
    (hxne : x ≠ a) (hyne : y ≠ a) (hbne : b ≠ a)
    (h : a ∈ segment ℝ (midpoint ℝ x y) b) : False := by
  have hxA : x ∈ (A : Set ℝ²) := by exact_mod_cast hx
  have hyA : y ∈ (A : Set ℝ²) := by exact_mod_cast hy
  have hbA : b ∈ (A : Set ℝ²) := by exact_mod_cast hb
  have hsub : ({x, y, b} : Set ℝ²) ⊆ (A : Set ℝ²) \ {a} := by
    intro p hp
    have hp' : p = x ∨ p = y ∨ p = b := by simpa using hp
    rcases hp' with rfl | rfl | rfl
    · refine ⟨hxA, ?_⟩
      simpa using hxne
    · refine ⟨hyA, ?_⟩
      simpa using hyne
    · refine ⟨hbA, ?_⟩
      simpa using hbne
  exact hA a (by exact_mod_cast ha)
    (convexHull_mono hsub (mem_convexHull_of_midpoint_segment h))

end Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexIndepHelpers
