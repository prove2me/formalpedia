-- Prove2me | solution 1 for Problem97.signedArea2_eq_zero_iff_collinear
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:07:06.675114+00:00
-- url     : https://prove2.me/submissions/a5a74e0e-9ce1-48e5-b993-859d4f355dcb

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.OangleBridge:24896:26851. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
import Mathlib.Geometry.Euclidean.Angle.Sphere
import Mathlib.Geometry.Euclidean.Simplex
import Theorems.Thm_Problem97_collinear_of_signedArea2_eq_zero

section Erdos9796CountingFragment_Erdos9796Proof_P97_OangleBridge

open Problem97

/- Fragment from Erdos9796Proof.P97.OangleBridge; source SHA-256 f9fbffddedb8e5ece4b3223e436c1d63e2482969b22da45c8d09d8cf9cefcef1 -/


/-!
# Oangle bridge: lift `dist` / `signedArea2` predicates to Mathlib `oangle` / `Cospherical`

This module supplies a small set of bridge lemmas that lift the project's
in-tree vocabulary on the MEC + Moser-triangle infrastructure to Mathlib's
oriented-angle (`EuclideanGeometry.oangle`), cospherical-set
(`EuclideanGeometry.Cospherical`), and equilateral-triangle
(`Affine.Simplex.Equilateral`) vocabulary.

The intended consumers are Phase 1 sublemma 5 ("short-cap Apollonius",
`U1ShortCapApollonius` in `U1TwoShortCapReduction`) and the related U2/U3
geometric content (`U2EquilateralMECFromM44`, `U3ShortCapSaturation`).

Scope of this pass (no proofs in U1/U2/U3 are modified by this file):

* `Problem97.MEC.moserTriangle_v{1,2,3}_mem_mecSphere` — concrete sphere
  membership of the three vertices of a `MoserTriangle`.
* `Problem97.MEC.moserTriangle_cospherical` — the abstract `Cospherical`
  predicate on the vertex-triple.
* `Problem97.MEC.moserTriangle_distinct_of_circumscribed`,
  `Problem97.MEC.moserTriangle_affineIndependent_of_circumscribed` —
  pairwise distinctness + affine independence in the circumscribed branch
  of the Sylvester dichotomy, needed for the oangle/Cospherical converse
  lemmas.
* `Problem97.two_zsmul_oangle_eq_of_mecSphere` — wraps mathlib's
  `Sphere.two_zsmul_oangle_eq` for points on the MEC sphere
  (inscribed-angle theorem in Mathlib's `2 • oangle = 2 • oangle` form).
* `Problem97.cospherical_of_two_zsmul_oangle_eq_of_not_collinear_named` —
  re-export of mathlib's Apollonius converse, named in our namespace so
  downstream callers don't have to chase the open-namespace boilerplate.

No proofs in this file rely on `sorry`, opaque `axiom`s, or vacuous
`True`-placeholders. The harder bridges (the explicit equilateral-side
formula `d = R · √3`, the full chord-side characterization of the 60°
Apollonius arc, the `Real.Angle.pi_div_three` arithmetic at an
equilateral inscribed apex, and the converse direction
`Collinear ↔ signedArea2 = 0`) are deliberately *not* included in this
pass — they remain open sub-obligations flagged in
`docs/97-uniform-theorem-closure-plan.md` Phase 1 sublemma 5 and
`docs/97-uniform-theorem-candidate.md`. -/

open scoped EuclideanGeometry





/- ### MEC + Moser-triangle vertices as `Cospherical` data -/









/- ### Distinctness extractors in the circumscribed branch

For all consumers below the diameter branch is `v3 = v1`; pairwise
distinctness only holds in the circumscribed branch. The
`NonObtuseCircumscribedMoserTriangle` wrapper produced by
`MoserTriangleNonObtuse` always sits in the circumscribed branch (built
from `exists_nonobtuse_circumscribed_triple`), but the `case_split`
witness is hidden inside the underlying `MoserTriangle`. The lemmas below
unpack pairwise distinctness from the `case_split` directly. -/







/- ### Inscribed-angle / Apollonius-converse bridges (in `Problem97` namespace)

These are direct wrappers of mathlib's `Sphere.two_zsmul_oangle_eq` and
`cospherical_of_two_zsmul_oangle_eq_of_not_collinear`, named so that
downstream callers can invoke them without re-opening
`EuclideanGeometry`. -/





/- ### Operational Apollonius-arc predicate

The placeholder `Problem97.Abstract60ApolloniusArc` in
`U3ShortCapSaturation` currently unfolds to `True`. The intended
operational form combines an inscribed-angle equality (in Mathlib's
`2 • oangle` form, which is the chart-free statement of "P sees `vj, vk`
at the same angle as `vi` does") with a chord-side condition pinning
`P` to the arc opposite `vi`.

`OpApolloniusArc vi vj vk P` is that operational form, expressed using:

* Mathlib's `EuclideanGeometry.oangle` (modular by `π`, so `2 • oangle`
  identifies the two arcs of a circle).
* The in-tree `Problem97.OnArcOpposite vi vj vk P` (signed-area chord
  side), which is the strict arc-side pin.

This file does not (yet) prove that `OpApolloniusArc` agrees with the
classical 60° arc through `vj, vk` opposite `vi` in the equilateral
inscribed setting. That equivalence is the load-bearing content of
Phase 1 sublemma 5; see
`docs/97-uniform-theorem-closure-plan.md` lines 213–217 and the
`Abstract60ApolloniusArc` `{{NEEDS_RESEARCH}}` marker at
`U3ShortCapSaturation.lean:114`. -/







/- ### Equilateral-inscribed bridge lemmas

These close the four deferred bridge lemmas flagged for Phase 1 of the
uniform-theorem closure plan (`docs/97-uniform-theorem-closure-plan.md`,
sublemma 5). They are stated in the general inner-product / sphere
setting so they can specialise to the MEC sphere `mecSphere A hA` (the
caller substitutes `s := mecSphere A hA`). Together with the existing
`cospherical_of_opApolloniusArc` forward direction, they constitute the
full characterisation of the 60° Apollonius arc:

* lemma 1 — equilateral inscribed side `= R · √3`;
* lemma 2 — equilateral inscribed apex sees the opposite chord at angle
  `π/3` (or, oriented, `(∡ p₁ p₂ p₃).toReal = ±π/3`);
* lemma 3 — cospherical implies the chart-free `2 • oangle` equality
  consumed by `OpApolloniusArc` (the reverse direction of the
  inscribed-angle bridge);
* lemma 4 — `signedArea2 v₁ v₂ v₃ = 0 ↔ Collinear ℝ {v₁, v₂, v₃}`
  (one direction is `MoserNonDeg.collinear_of_signedArea2_eq_zero`;
  this file supplies the converse). -/







/- The unsigned theorem above leaves the orientation branch to each caller.
   This small adapter discharges the negative branch from a positive signed
   angle hypothesis, which is the form supplied by the convex cyclic-order
   API. -/










theorem solution (v₁ v₂ v₃ : ℝ²) :
    signedArea2 v₁ v₂ v₃ = 0 ↔ Collinear ℝ ({v₁, v₂, v₃} : Set ℝ²) := by
  refine ⟨collinear_of_signedArea2_eq_zero v₁ v₂ v₃, ?_⟩
  intro hcol
  rw [collinear_iff_of_mem (Set.mem_insert v₁ _)] at hcol
  obtain ⟨d, hd⟩ := hcol
  obtain ⟨r₂, hr₂⟩ := hd v₂ (Set.mem_insert_of_mem _ (Set.mem_insert v₂ _))
  obtain ⟨r₃, hr₃⟩ := hd v₃
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hv₂ : v₂ - v₁ = r₂ • d := by rw [hr₂]; simp [vadd_eq_add]
  have hv₃ : v₃ - v₁ = r₃ • d := by rw [hr₃]; simp [vadd_eq_add]
  have hv₂_0 : v₂ 0 - v₁ 0 = r₂ * d 0 := by
    have := congr_arg (· 0) hv₂; simp at this; linarith
  have hv₂_1 : v₂ 1 - v₁ 1 = r₂ * d 1 := by
    have := congr_arg (· 1) hv₂; simp at this; linarith
  have hv₃_0 : v₃ 0 - v₁ 0 = r₃ * d 0 := by
    have := congr_arg (· 0) hv₃; simp at this; linarith
  have hv₃_1 : v₃ 1 - v₁ 1 = r₃ * d 1 := by
    have := congr_arg (· 1) hv₃; simp at this; linarith
  unfold signedArea2
  rw [hv₂_0, hv₂_1, hv₃_0, hv₃_1]; ring

end Erdos9796CountingFragment_Erdos9796Proof_P97_OangleBridge
