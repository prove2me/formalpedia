-- Prove2me | solution 1 for Problem97.ConvexIndep.not_wbtw
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:10.594775+00:00
-- url     : https://prove2.me/submissions/c17932b0-3c8e-40b4-890f-a022b2b1b520

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.ConvexIndepHelpers:1552:2518. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation

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










theorem solution {A : Finset ℝ²} (hA : ConvexIndep A)
    {x y z : ℝ²} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : Wbtw ℝ x y z) (hyx : y ≠ x) (hyz : y ≠ z) : False := by
  have hmem : y ∈ convexHull ℝ ({x, z} : Set ℝ²) := by
    rw [convexHull_pair]
    exact hxy.mem_segment
  have hsub : ({x, z} : Set ℝ²) ⊆ (A : Set ℝ²) \ {y} := by
    intro p hp
    have hp' : p = x ∨ p = z := by simpa using hp
    rcases hp' with hpx | hpz
    · refine ⟨?_, ?_⟩
      · simpa [hpx] using hx
      · intro hy'
        have hyx' : x = y := by simpa [hpx] using hy'
        exact hyx hyx'.symm
    · refine ⟨?_, ?_⟩
      · simpa [hpz] using hz
      · intro hy'
        have hyz' : z = y := by simpa [hpz] using hy'
        exact hyz hyz'.symm
  exact hA y (by exact_mod_cast hy) (convexHull_mono hsub hmem)

end Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexIndepHelpers
