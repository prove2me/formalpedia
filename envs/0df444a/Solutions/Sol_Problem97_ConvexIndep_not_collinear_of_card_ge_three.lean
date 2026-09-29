-- Prove2me | solution 1 for Problem97.ConvexIndep.not_collinear_of_card_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:47.401421+00:00
-- url     : https://prove2.me/submissions/8cae150e-f71a-4a1c-981e-388f37180a34

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.ConvexIndepHelpers:5834:6743. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Theorems.Thm_Problem97_ConvexIndep_not_wbtw

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







/-- CGN2a: three collinear points have a weakly-between middle point. -/
theorem Problem97.collinear_three_wbtw {x y z : ℝ²}
    (hcol : Collinear ℝ ({x, y, z} : Set ℝ²)) :
    Wbtw ℝ x y z ∨ Wbtw ℝ y z x ∨ Wbtw ℝ z x y := by
  simpa using hcol.wbtw_or_wbtw_or_wbtw



/-- CGN5b: no line contains three distinct points of a convex-independent
finite set. -/
theorem Problem97.ConvexIndep.not_three_collinear {A : Finset ℝ²}
    (hA : ConvexIndep A) {x y z : ℝ²} (hx : x ∈ A) (hy : y ∈ A)
    (hz : z ∈ A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcol : Collinear ℝ ({x, y, z} : Set ℝ²)) : False := by
  rcases collinear_three_wbtw hcol with hw | hw | hw
  · exact hA.not_wbtw hx hy hz hw hxy.symm hyz
  · exact hA.not_wbtw hy hz hx hw hyz.symm hxz.symm
  · exact hA.not_wbtw hz hx hy hw hxz hxy








theorem solution {A : Finset ℝ²}
    (hA : ConvexIndep A) (hcard : 3 ≤ A.card) :
    ¬ Collinear ℝ (A : Set ℝ²) := by
  intro hcol
  have hgt : 2 < A.card := lt_of_lt_of_le (by decide : 2 < 3) hcard
  rcases Finset.two_lt_card.mp hgt with
    ⟨x, hxA, y, hyA, z, hzA, hxy, hxz, hyz⟩
  have hsubset : ({x, y, z} : Set ℝ²) ⊆ (A : Set ℝ²) := by
    intro p hp
    have hp' : p = x ∨ p = y ∨ p = z := by simpa using hp
    rcases hp' with hpx | hpy | hpz
    · simpa [hpx] using hxA
    · simpa [hpy] using hyA
    · simpa [hpz] using hzA
  have hcol3 : Collinear ℝ ({x, y, z} : Set ℝ²) :=
    Collinear.subset hsubset hcol
  exact hA.not_three_collinear hxA hyA hzA hxy hxz hyz hcol3

end Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexIndepHelpers
