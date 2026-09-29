-- Prove2me | solution 1 for Problem97.CGN.CGN6e2_not_two_apices_on_complementary_side
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:07:16.090574+00:00
-- url     : https://prove2.me/submissions/ebfdad4a-138b-48d8-bbce-a5368944e6ea

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN6:89413:91304. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Order.Interval.Finset.Fin
import Theorems.Thm_Problem97_CGN_CGN6d0_positiveSideBisector_to_wbtw
import Theorems.Thm_Problem97_ConvexIndep_not_same_ray_perpBisector

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

















/-- CGN6d wrapper: the same-ray contradiction stated with `Wbtw`. -/
theorem Problem97.ConvexIndep.not_same_ray_perpBisector_of_wbtw {A : Finset ℝ²}
    (hA : ConvexIndep A) {x y a b : ℝ²}
    (hx : x ∈ A) (hy : y ∈ A) (ha : a ∈ A) (hb : b ∈ A)
    (hxne : x ≠ a) (hyne : y ≠ a) (hbne : b ≠ a)
    (h : Wbtw ℝ (midpoint ℝ x y) a b) : False :=
  hA.not_same_ray_perpBisector hx hy ha hb hxne hyne hbne h.mem_segment

end Erdos9796CountingFragment_Erdos9796Proof_P97_ConvexIndepHelpers

section Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN6

open Problem97 Problem97.CGN

/- Fragment from Erdos9796Proof.P97.CGN.CGN6; source SHA-256 87eeea2860c10b6c484c3d7aec9f295605a553c9956e5cc04bbc649402bc9c30 -/


/-!
# CGN6: normalized minor-cap chain model

This file starts the CGN6 layer named in the updated counterexample-card-ge-nine
prose. It records the normalized minor-cap chain data the prose uses for the
CGN6b slope-product argument: ordered coordinates, endpoint normalization, the
unit-disk bound, and the adjacent-slope bookkeeping.

The actual geometric construction of this model from a concrete MEC cap packet
is still separate. This file only provides the data interface the subsequent
CGN6b / CGN6c proofs will consume.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators


























/- ### CGN6norm scaffold

The prose normalization theorem uses an explicit coordinate frame
centered at the chord midpoint and aligned with the chord / inward
normal directions.  The full packet-to-frame bridge is still separate;
this helper records the coordinate map in the exact algebraic form used
by the prose.
-/































-- The normalization proof is large enough to need a higher elaboration budget.


























/-- Swapping the first two arguments of `signedArea2` negates its value. -/
 theorem Problem97.CGN.signedArea2_swap (x y z : ℝ²) :
    signedArea2 x y z = - signedArea2 y x z := by
  unfold signedArea2
  ring


theorem solution
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (hconv : ConvexIndep A) (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s) {a b : ℝ²}
    (haA : a ∈ A) (hbA : b ∈ A)
    (hab : a ≠ b)
    (har : a ≠ L.points r) (has : a ≠ L.points s)
    (hbr : b ≠ L.points r) (hbs : b ≠ L.points s)
    (haeq : dist a (L.points r) = dist a (L.points s))
    (hbeq : dist b (L.points r) = dist b (L.points s))
    (ha_neg : signedArea2 (L.points r) (L.points s) a < 0)
    (hb_neg : signedArea2 (L.points r) (L.points s) b < 0) :
    False := by
  have hxy : L.points s ≠ L.points r := by
    intro h
    exact (ne_of_lt hrs) (Eq.symm (L.injective h))
  have ha_pos : 0 < signedArea2 (L.points s) (L.points r) a := by
    rw [Problem97.CGN.signedArea2_swap]
    linarith
  have hb_pos : 0 < signedArea2 (L.points s) (L.points r) b := by
    rw [Problem97.CGN.signedArea2_swap]
    linarith
  have hwt :
      Wbtw ℝ (midpoint ℝ (L.points s) (L.points r)) a b ∨
        Wbtw ℝ (midpoint ℝ (L.points s) (L.points r)) b a :=
    CGN6d0_positiveSideBisector_to_wbtw
      (x := L.points s) (y := L.points r)
      hxy haeq.symm hbeq.symm ha_pos hb_pos
  have hsA : L.points s ∈ A := hmem s
  have hrA : L.points r ∈ A := hmem r
  rcases hwt with hwt | hwt
  · have hxne : L.points s ≠ a := by
      exact has.symm
    have hyne : L.points r ≠ a := by
      exact har.symm
    have hbne : b ≠ a := hab.symm
    exact hconv.not_same_ray_perpBisector_of_wbtw hsA hrA haA hbA hxne hyne hbne hwt
  · have hxne : L.points s ≠ b := by
      exact hbs.symm
    have hyne : L.points r ≠ b := by
      exact hbr.symm
    have hbne : a ≠ b := hab
    exact hconv.not_same_ray_perpBisector_of_wbtw hsA hrA hbA haA hxne hyne hbne hwt

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN6
