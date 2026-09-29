-- Prove2me | solution 1 for Problem97.CGN.CGN6d0_positiveSideBisector_to_wbtw
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:07:09.732633+00:00
-- url     : https://prove2.me/submissions/e07ab461-5edb-41c1-9525-fd8d89fff0b0

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN6:82167:87665. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Order.Interval.Finset.Fin
import Theorems.Thm_Problem97_signedArea2_eq_zero_iff_collinear

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







/-- CGN2a: three collinear points have a weakly-between middle point. -/
theorem Problem97.collinear_three_wbtw {x y z : ℝ²}
    (hcol : Collinear ℝ ({x, y, z} : Set ℝ²)) :
    Wbtw ℝ x y z ∨ Wbtw ℝ y z x ∨ Wbtw ℝ z x y := by
  simpa using hcol.wbtw_or_wbtw_or_wbtw

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





















theorem solution
    {x y a b : ℝ²}
    (hx : x ≠ y)
    (haeq : dist a x = dist a y)
    (hbeq : dist b x = dist b y)
    (ha_pos : 0 < signedArea2 x y a)
    (hb_pos : 0 < signedArea2 x y b) :
    Wbtw ℝ (midpoint ℝ x y) a b ∨ Wbtw ℝ (midpoint ℝ x y) b a := by
  have hm : midpoint ℝ x y ∈ affineSpan ℝ ({x, y} : Set ℝ²) := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨(1 / 2 : ℝ), ?_⟩
    rw [midpoint_eq_smul_add]
    simp [AffineMap.lineMap]
    module
  have hcol_xy_mid : Collinear ℝ ({x, y, midpoint ℝ x y} : Set ℝ²) := by
    have hcol' : Collinear ℝ ({midpoint ℝ x y, x, y} : Set ℝ²) := by
      exact collinear_insert_of_mem_affineSpan_pair
        (p₁ := midpoint ℝ x y) (p₂ := x) (p₃ := y) hm
    have hset : ({midpoint ℝ x y, x, y} : Set ℝ²) = ({x, y, midpoint ℝ x y} : Set ℝ²) := by
      ext p
      simp [or_comm, or_assoc]
    simpa [hset] using hcol'
  have hmid_area : signedArea2 x y (midpoint ℝ x y) = 0 := by
    exact (Problem97.signedArea2_eq_zero_iff_collinear x y (midpoint ℝ x y)).2 hcol_xy_mid
  have haP : a ∈ AffineSubspace.perpBisector x y := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
    exact haeq
  have hbP : b ∈ AffineSubspace.perpBisector x y := by
    rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
    exact hbeq
  have hmP : midpoint ℝ x y ∈ AffineSubspace.perpBisector x y := by
    exact AffineSubspace.midpoint_mem_perpBisector x y
  have hane : a -ᵥ midpoint ℝ x y ≠ 0 := by
    intro h
    have ha_mid : a = midpoint ℝ x y := (vsub_eq_zero_iff_eq).mp h
    subst ha_mid
    linarith
  haveI : Fact (Module.finrank ℝ ℝ² = 1 + 1) := ⟨by
    simpa using (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2))⟩
  have hdir_finrank : Module.finrank ℝ (AffineSubspace.perpBisector x y).direction = 1 := by
    rw [AffineSubspace.direction_perpBisector]
    have hxyvec : y -ᵥ x ≠ 0 := by
      intro h
      exact hx ((vsub_eq_zero_iff_eq).mp h).symm
    exact Submodule.finrank_orthogonal_span_singleton (v := y -ᵥ x) hxyvec
  have hdir_le : ℝ ∙ (a -ᵥ midpoint ℝ x y) ≤ (AffineSubspace.perpBisector x y).direction := by
    rw [AffineSubspace.direction_perpBisector]
    exact (Submodule.span_singleton_le_iff_mem _ _).2
      (by simpa [AffineSubspace.direction_perpBisector] using
        (AffineSubspace.vsub_mem_direction haP hmP))
  have hdir_eq : ℝ ∙ (a -ᵥ midpoint ℝ x y) = (AffineSubspace.perpBisector x y).direction := by
    apply Submodule.eq_of_le_of_finrank_eq hdir_le
    rw [finrank_span_singleton hane, hdir_finrank]
  have hbspan : b -ᵥ midpoint ℝ x y ∈ ℝ ∙ (a -ᵥ midpoint ℝ x y) := by
    rw [hdir_eq]
    simpa [AffineSubspace.direction_perpBisector] using
      (AffineSubspace.vsub_mem_direction hbP hmP)
  rcases Submodule.mem_span_singleton.mp hbspan with ⟨r, hr⟩
  have hcol : Collinear ℝ ({a, midpoint ℝ x y, b} : Set ℝ²) := by
    rw [collinear_iff_of_mem (by
      simp : midpoint ℝ x y ∈ ({a, midpoint ℝ x y, b} : Set ℝ²))]
    refine ⟨a -ᵥ midpoint ℝ x y, ?_⟩
    intro p hp
    rcases hp with rfl | rfl | rfl
    · refine ⟨1, ?_⟩
      simp
    · refine ⟨0, ?_⟩
      simp
    · refine ⟨r, ?_⟩
      exact (eq_vadd_iff_vsub_eq p (r • (a -ᵥ midpoint ℝ x y))
        (midpoint ℝ x y)).2 hr.symm
  rcases Problem97.collinear_three_wbtw hcol with h1 | h2 | h3
  · exfalso
    let l : ℝ² →ₗ[ℝ] ℝ :=
      { toFun := fun v => signedArea2 x y v - signedArea2 x y 0
        map_add' := by
          intro u v
          simp [signedArea2]
          ring
        map_smul' := by
          intro c v
          simp [signedArea2]
          ring }
    let f : ℝ² →ᵃ[ℝ] ℝ :=
      AffineMap.mk' (fun p => signedArea2 x y p) l 0 (by
        intro p
        simp [l])
    have hmap : Wbtw ℝ (f a) (f (midpoint ℝ x y)) (f b) := Wbtw.map h1 f
    change Wbtw ℝ (signedArea2 x y a) (signedArea2 x y (midpoint ℝ x y))
      (signedArea2 x y b) at hmap
    rw [hmid_area] at hmap
    have hseg : 0 ∈ segment ℝ (signedArea2 x y a) (signedArea2 x y b) := hmap.mem_segment
    rw [segment_eq_image] at hseg
    rcases hseg with ⟨θ, hθ, heq⟩
    have hpos : 0 < (1 - θ) * signedArea2 x y a + θ * signedArea2 x y b := by
      have hθ0 : 0 ≤ θ := hθ.1
      have hθ1 : θ ≤ 1 := hθ.2
      by_cases hθz : θ = 0
      · subst hθz
        simpa using ha_pos
      · by_cases hθ1' : θ = 1
        · subst hθ1'
          simpa using hb_pos
        · have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθz)
          have hθlt : θ < 1 := lt_of_le_of_ne hθ1 hθ1'
          have h1' : 0 < (1 - θ) * signedArea2 x y a := by
            have h : 0 < 1 - θ := by nlinarith [hθlt]
            exact mul_pos h ha_pos
          have h2' : 0 < θ * signedArea2 x y b := mul_pos hθpos hb_pos
          exact add_pos h1' h2'
    have heq' : (1 - θ) * signedArea2 x y a + θ * signedArea2 x y b = 0 := by
      simpa [smul_eq_mul] using heq
    exact (ne_of_gt hpos) heq'
  · exact Or.inr h2
  · exact Or.inl (Wbtw.symm h3)

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN6
