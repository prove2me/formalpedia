-- Prove2me | solution 1 for Problem97.CGN.CGN6norm_minorCapChainModel_of_mecCapPacket
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T05:57:13.143308+00:00
-- url     : https://prove2.me/submissions/988f0d8f-d9b1-4423-b154-fa508e1328bc

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN6:17365:43446. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN6
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_SignedAreaOangle
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Order.Interval.Finset.Fin

section Erdos9796CountingFragment_Erdos9796Proof_P97_Foundation

open Problem97

/- Fragment from Erdos9796Proof.P97.Foundation; source SHA-256 a391c93c43d33614d2c04166d97d6a5d88b750a5691b6c682233c1d1c9de9bd3 -/


/-!
# Foundation: shared vocabulary for the Erdős Problem 97 universal proof

All definitions are thin abbreviations of the upstream declarations in
`flound1129/formal-conjectures` (branch `erdos96-formalization`):

* `ℝ²` (scoped notation in `EuclideanGeometry`) — the ambient plane.
* `Erdos97.HasNEquidistantPointsAt/On/Property` — the equidistant predicates.
* `EuclideanGeometry.ConvexIndep` — convex independence as the extreme-point
  property `∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})`, on `Set ℝ²`.

Our `Problem97.*` namespace exists only to host the universal-descent
assembly (`UniversalProblem97_of_reduction`) and helper lemmas in a private
working namespace; it does **not** redefine any predicate.
-/

open scoped EuclideanGeometry



export Erdos97 (HasNEquidistantPointsAt HasNEquidistantPointsOn HasNEquidistantProperty)

/-- Coordinate expansion of squared distance on `ℝ²`. -/
theorem Problem97.dist_sq_coord (x y : ℝ²) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]











/- ### Signed-area arc-side predicate

A lightweight algebraic predicate for "point `v` lies on the closed MEC arc
from `vj` to `vk` not passing through `vi`," used by the strengthened
`CapTriple` to pin caps to actual arcs cut by a Moser triangle. The
signed-area form avoids any `CircularOrder ℝ²` machinery — `v` and `vi`
must lie on opposite (closed) sides of the chord `vj`—`vk`. The
closed-cap convention is built in: equality (point on the chord) puts
the point on *both* sides, which is what closed caps need at endpoints.
-/

end Erdos9796CountingFragment_Erdos9796Proof_P97_Foundation

section Erdos9796CountingFragment_Erdos9796Proof_P97_SignedAreaOangle

open Problem97

/- Fragment from Erdos9796Proof.P97.SignedAreaOangle; source SHA-256 b3d7d5da8bb313997dd505e15b0ba2823db075ab8d863e995246ecbcce8f4fa9 -/


/-!
# Bridge: algebraic `signedArea2` ↔ Mathlib oriented angle sign

This module supplies the foundational bridge consumed by the MEC arc–angle
chain (sub-obligation `p97-signed-area-eq-oangle-sign`, alias A.1). The
algebraic predicate `Problem97.signedArea2` defined in `Foundation` is the
chord-side / signed-area form used by the cap-witness machinery. The MEC
parametrization, in contrast, needs Mathlib's oriented angle
`Orientation.oangle` on the standard counter-clockwise orientation of
`ℝ² = EuclideanSpace ℝ (Fin 2)`. Both quantities carry the *same sign* by a
direct computation: `signedArea2` is exactly the area form of the standard
orientation evaluated on the two chord vectors, and `oangle` is the
`Complex.arg` of the Kähler form whose imaginary part is that area form.

The single externally-used result is `signedArea2_sign_eq_oangle_sign`
(plus its `Real.sign` cast variant). All proofs are by direct Mathlib
manipulation; no new axioms are introduced.
-/

open scoped EuclideanGeometry





/-- The algebraic `signedArea2` is exactly the area form of the standard
orientation evaluated on the chord vectors `vj - v` and `vk - v`. -/
theorem Problem97.signedArea2_eq_stdOrientation_areaForm (v vj vk : ℝ²) :
    Problem97.signedArea2 v vj vk =
      stdOrientation.areaForm (vj - v) (vk - v) := by
  rw [stdOrientation, Orientation.areaForm_to_volumeForm,
      Orientation.volumeForm_robust _ (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
      Module.Basis.det_apply]
  simp only [Module.Basis.toMatrix_apply, Matrix.det_fin_two, signedArea2,
             EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr,
             Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.sub_apply]

end Erdos9796CountingFragment_Erdos9796Proof_P97_SignedAreaOangle

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







/-- A vector in `ℝ²` is the sum of its coordinates in an orthonormal pair. -/
 theorem Problem97.CGN.orthonormal_pair_decomp {e n x : ℝ²}
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) :
    x = inner ℝ e x • e + inner ℝ n x • n := by
  classical
  have hpair : Orthonormal ℝ (fun i : Fin 2 => if i = 0 then e else n) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [he, hn, hen, real_inner_comm]
  let b : Module.Basis (Fin 2) ℝ ℝ² :=
    basisOfOrthonormalOfCardEqFinrank
      hpair
      (by simp)
  have hb : Orthonormal ℝ ⇑b := by
    simpa [b] using hpair
  let ob : OrthonormalBasis (Fin 2) ℝ ℝ² := b.toOrthonormalBasis hb
  calc
    x = ∑ i : Fin 2, inner ℝ (ob i) x • ob i := by
      have h := ob.sum_repr' x
      simpa [ob, b] using h.symm
    _ = inner ℝ e x • e + inner ℝ n x • n := by
      simp [ob, b, Fin.sum_univ_two]

/-- Squared norm in an orthonormal pair is the sum of squared coordinates. -/
 theorem Problem97.CGN.orthonormal_pair_normsq {e n x : ℝ²}
    (he : ‖e‖ = 1) (hn : ‖n‖ = 1) (hen : inner ℝ e n = 0) :
    ‖x‖ ^ 2 = (inner ℝ e x)^2 + (inner ℝ n x)^2 := by
  have hdecomp := Problem97.CGN.orthonormal_pair_decomp (e := e) (n := n) he hn hen (x := x)
  rw [hdecomp]
  have horth : inner ℝ (inner ℝ e x • e) (inner ℝ n x • n) = 0 := by
    simp [real_inner_smul_left, real_inner_smul_right, hen]
  have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (inner ℝ e x • e) (inner ℝ n x • n) horth
  have hinner_e : inner ℝ e (inner ℝ e x • e + inner ℝ n x • n) = inner ℝ e x := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    simp [he, hen]
  have hinner_n : inner ℝ n (inner ℝ e x • e + inner ℝ n x • n) = inner ℝ n x := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    simp [hn, hen, real_inner_comm]
  simpa [hinner_e, hinner_n, norm_smul, he, hn, pow_two] using hsq







/-- The `chordFrame` map is linear when the midpoint is `0`. -/
 noncomputable def Problem97.CGN.chordLinear (e n : ℝ²) (scale : ℝ) : ℝ² →ₗ[ℝ] ℝ² where
  toFun := fun v => chordFrame (0 : ℝ²) e n scale v
  map_add' := by
    intro x y
    ext i <;> fin_cases i <;> simp [chordFrame, inner_add_left, inner_add_right]
    all_goals ring
  map_smul' := by
    intro m x
    ext i <;> fin_cases i <;> simp [chordFrame, inner_smul_left, inner_smul_right]
    all_goals ring

/-- Area-form identity for the standard orientation and the right-angle
rotation of a unit vector. -/
 theorem Problem97.CGN.orthonormal_areaForm (e : ℝ²) (he : ‖e‖ = 1) :
    ∀ u v : ℝ²,
      Problem97.stdOrientation.areaForm u v =
        ⟪u, e⟫_ℝ * ⟪v, Problem97.stdOrientation.rightAngleRotation e⟫_ℝ -
        ⟪u, Problem97.stdOrientation.rightAngleRotation e⟫_ℝ * ⟪v, e⟫_ℝ := by
  let n : ℝ² := Problem97.stdOrientation.rightAngleRotation e
  have hn : ‖n‖ = 1 := by
    simpa [n, he] using Problem97.stdOrientation.rightAngleRotation.norm_map e
  have hen : inner ℝ e n = 0 := by
    simpa [n, real_inner_comm] using Problem97.stdOrientation.inner_rightAngleRotation_self e
  have hEn : Problem97.stdOrientation.areaForm e n = 1 := by
    simpa [n, he] using
      (Problem97.stdOrientation.areaForm_rightAngleRotation_right (x := e) (y := e))
  have harea_e : ∀ v : ℝ², Problem97.stdOrientation.areaForm e v = ⟪v, n⟫_ℝ := by
    intro v
    have h' : Problem97.stdOrientation.areaForm e v =
        ⟪v, Problem97.stdOrientation.rightAngleRotation e⟫_ℝ := by
      have h := Problem97.stdOrientation.inner_rightAngleRotation_right (x := v) (y := e)
      rw [Problem97.stdOrientation.areaForm_swap] at h
      simpa using h.symm
    simpa [n] using h' 
  have harea_n : ∀ v : ℝ², Problem97.stdOrientation.areaForm n v = -⟪v, e⟫_ℝ := by
    intro v
    have h' : Problem97.stdOrientation.areaForm
        (Problem97.stdOrientation.rightAngleRotation e) v = -⟪v, e⟫_ℝ := by
      have h := Problem97.stdOrientation.inner_rightAngleRotation_left
        (x := Problem97.stdOrientation.rightAngleRotation e) (y := v)
      simpa [real_inner_comm] using h
    simpa [n] using h'
  intro u v
  have hu := Problem97.CGN.orthonormal_pair_decomp (e := e) (n := n) he hn hen (x := u)
  have htmp1 : Problem97.stdOrientation.areaForm (⟪e, u⟫_ℝ • e) =
      ⟪e, u⟫_ℝ • Problem97.stdOrientation.areaForm e := by
    exact LinearMap.map_smul (Problem97.stdOrientation.areaForm) (⟪e, u⟫_ℝ) e
  have htmp2 : Problem97.stdOrientation.areaForm (⟪n, u⟫_ℝ • n) =
      ⟪n, u⟫_ℝ • Problem97.stdOrientation.areaForm n := by
    exact LinearMap.map_smul (Problem97.stdOrientation.areaForm) (⟪n, u⟫_ℝ) n
  have h1 : Problem97.stdOrientation.areaForm (⟪e, u⟫_ℝ • e) v =
      ⟪e, u⟫_ℝ * ⟪v, n⟫_ℝ := by
    have := congrArg (fun z : ℝ² →ₗ[ℝ] ℝ => z v) htmp1
    simpa [harea_e v] using this
  have h2 : Problem97.stdOrientation.areaForm (⟪n, u⟫_ℝ • n) v =
      -⟪n, u⟫_ℝ * ⟪v, e⟫_ℝ := by
    have := congrArg (fun z : ℝ² →ₗ[ℝ] ℝ => z v) htmp2
    simpa [harea_n v] using this
  have hsum :
      Problem97.stdOrientation.areaForm
          (⟪e, u⟫_ℝ • e + ⟪n, u⟫_ℝ • n) v =
        ⟪e, u⟫_ℝ * ⟪v, n⟫_ℝ - ⟪n, u⟫_ℝ * ⟪v, e⟫_ℝ := by
    have htmp :
        Problem97.stdOrientation.areaForm
          (⟪e, u⟫_ℝ • e + ⟪n, u⟫_ℝ • n) =
        Problem97.stdOrientation.areaForm (⟪e, u⟫_ℝ • e) +
          Problem97.stdOrientation.areaForm (⟪n, u⟫_ℝ • n) := by
      exact LinearMap.map_add (Problem97.stdOrientation.areaForm)
        (⟪e, u⟫_ℝ • e) (⟪n, u⟫_ℝ • n)
    have := congrArg (fun z : ℝ² →ₗ[ℝ] ℝ => z v) htmp
    change (Problem97.stdOrientation.areaForm
      (⟪e, u⟫_ℝ • e + ⟪n, u⟫_ℝ • n)) v =
      (Problem97.stdOrientation.areaForm (⟪e, u⟫_ℝ • e)) v +
        (Problem97.stdOrientation.areaForm (⟪n, u⟫_ℝ • n)) v at this
    rw [h1, h2] at this
    simpa [sub_eq_add_neg] using this
  have hrew : Problem97.stdOrientation.areaForm u v =
      Problem97.stdOrientation.areaForm
        (⟪e, u⟫_ℝ • e + ⟪n, u⟫_ℝ • n) v := by
    simpa using congrArg (fun z : ℝ² => Problem97.stdOrientation.areaForm z v) hu
  have hfinal : Problem97.stdOrientation.areaForm u v =
      ⟪u, e⟫_ℝ * ⟪v, n⟫_ℝ - ⟪u, n⟫_ℝ * ⟪v, e⟫_ℝ := by
    calc
      Problem97.stdOrientation.areaForm u v =
          Problem97.stdOrientation.areaForm
            (⟪e, u⟫_ℝ • e + ⟪n, u⟫_ℝ • n) v := hrew
      _ = ⟪e, u⟫_ℝ * ⟪v, n⟫_ℝ - ⟪n, u⟫_ℝ * ⟪v, e⟫_ℝ := hsum
      _ = ⟪u, e⟫_ℝ * ⟪v, n⟫_ℝ - ⟪u, n⟫_ℝ * ⟪v, e⟫_ℝ := by
        rw [real_inner_comm (x := e) (y := u), real_inner_comm (x := n) (y := u)]
  simpa [n] using hfinal

/-- Area-form formula for `vec2`. -/
 theorem Problem97.CGN.vec2_areaForm (a b c d : ℝ) :
    Problem97.stdOrientation.areaForm (vec2 a b) (vec2 c d) = a * d - b * c := by
  have h := Problem97.signedArea2_eq_stdOrientation_areaForm (v := (0 : ℝ²))
    (vj := vec2 a b) (vk := vec2 c d)
  have h' : Problem97.stdOrientation.areaForm (vec2 a b) (vec2 c d) =
      Problem97.signedArea2 (0 : ℝ²) (vec2 a b) (vec2 c d) := by
    simpa [vec2, sub_eq_add_neg] using h.symm
  rw [h']
  simp [Problem97.signedArea2, vec2]
  ring_nf

/-- Distance-squared formula for `vec2`. -/
 theorem Problem97.CGN.vec2_dist_sq (x1 y1 x2 y2 : ℝ) :
    dist (vec2 x1 y1) (vec2 x2 y2) ^ 2 = (x1 - x2) ^ 2 + (y1 - y2) ^ 2 := by
  simpa [vec2, EuclideanSpace.single_apply] using
    Problem97.dist_sq_coord (vec2 x1 y1) (vec2 x2 y2)

/-- Rewrite a coordinate-indexed point as the corresponding `vec2` value. -/
 theorem Problem97.CGN.point_eq_vec2 {m : ℕ} (X Y : Fin m → ℝ) (t : Fin m) :
    point X Y t = vec2 (X t) (Y t) := by
  ext i <;> fin_cases i <;>
    simp [point, vec2, EuclideanSpace.single_apply]

/-- Expand the signed area of three coordinate-indexed points into coordinate
   differences. -/
 theorem Problem97.CGN.point_signedArea2_eq {m : ℕ} (X Y : Fin m → ℝ) (t0 t1 t2 : Fin m) :
    signedArea2 (point X Y t0) (point X Y t1) (point X Y t2) =
      (X t1 - X t0) * (Y t2 - Y t1) - (Y t1 - Y t0) * (X t2 - X t1) := by
  rw [Problem97.CGN.point_eq_vec2 X Y t0, Problem97.CGN.point_eq_vec2 X Y t1, Problem97.CGN.point_eq_vec2 X Y t2]
  simp [Problem97.signedArea2, vec2]
  ring

/-- Scaled area-form formula for `vec2`. -/
 theorem Problem97.CGN.vec2_areaForm_scaled (a b c d scale : ℝ) :
    Problem97.stdOrientation.areaForm
        (vec2 (scale * a) (scale * b))
        (vec2 (scale * c) (scale * d)) =
      scale ^ 2 * (a * d - b * c) := by
  have h := Problem97.CGN.vec2_areaForm (a := scale * a) (b := scale * b) (c := scale * c) (d := scale * d)
  have h' : (scale * a) * (scale * d) - (scale * b) * (scale * c) =
      scale ^ 2 * (a * d - b * c) := by
    ring
  exact h.trans h'

-- The normalization proof is large enough to need a higher elaboration budget.
set_option maxHeartbeats 600000 in

theorem solution
    {A : Finset ℝ²} {m : ℕ} {L : OrderedCap m}
    (Packet : MecCapPacket A L)
    (Hside : MinorCapSideHypotheses Packet)
    (Hord : StrictCapOrder A L) :
    ∃ T, ∃ hT : Function.Injective T, ∃ tau : SimilarityTransportData T,
      Nonempty (MinorCapChainModel (L.map T hT)) := by
  classical
  let q1 : ℝ² := L.points (firstIndex (m := m) Packet.hm)
  let qm : ℝ² := L.points (lastIndex (m := m) Packet.hm)
  have hfirst_last : firstIndex (m := m) Packet.hm ≠ lastIndex (m := m) Packet.hm := by
    intro h
    have hm1 : 1 < m := by
      exact Packet.hm
    have hval0 : (firstIndex (m := m) Packet.hm).val = 0 := by simp [firstIndex]
    have hval1 : (lastIndex (m := m) Packet.hm).val = m - 1 := by simp [lastIndex]
    have hne : m - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hm1
    have hval : (0 : ℕ) = m - 1 := by
      simpa [hval0, hval1] using congrArg Fin.val h
    exact hne hval.symm
  have hqne : q1 ≠ qm := by
    intro hq
    exact hfirst_last (L.injective hq)
  let u : ℝ² := qm - q1
  have hu : u ≠ 0 := by
    dsimp [u]
    exact sub_ne_zero.mpr hqne.symm
  have hu_norm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let e : ℝ² := ‖u‖⁻¹ • u
  let n : ℝ² := Problem97.stdOrientation.rightAngleRotation e
  have he : ‖e‖ = 1 := by
    dsimp [e]
    have hnonneg : 0 ≤ ‖u‖⁻¹ := by positivity
    calc
      ‖e‖ = ‖‖u‖⁻¹ • u‖ := rfl
      _ = ‖u‖⁻¹ * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg]
      _ = 1 := by field_simp [hu_norm.ne']
  have hn : ‖n‖ = 1 := by
    simpa [n, he] using Problem97.stdOrientation.rightAngleRotation.norm_map e
  have hen : inner ℝ e n = 0 := by
    simpa [n, real_inner_comm] using Problem97.stdOrientation.inner_rightAngleRotation_self e
  let scale : ℝ := 2 / ‖u‖
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  let F : ℝ² →ₗ[ℝ] ℝ² := Problem97.CGN.chordLinear e n scale
  have hF_inj : Function.Injective F := by
    intro v w hfw
    have h0 : F (v - w) = 0 := by
      simpa [map_sub, hfw] using congrArg (fun z => z - F w) hfw
    have hcoord0 : scale * ⟪v - w, e⟫_ℝ = 0 := by
      have := congrArg (fun z : ℝ² => z 0) h0
      simpa [F, Problem97.CGN.chordLinear, chordFrame] using this
    have hcoord1 : scale * ⟪v - w, n⟫_ℝ = 0 := by
      have := congrArg (fun z : ℝ² => z 1) h0
      simpa [F, Problem97.CGN.chordLinear, chordFrame] using this
    have hv0 : ⟪e, v - w⟫_ℝ = 0 := by
      simpa [real_inner_comm] using
        (mul_eq_zero.mp hcoord0).resolve_left (by positivity)
    have hv1 : ⟪n, v - w⟫_ℝ = 0 := by
      simpa [real_inner_comm] using
        (mul_eq_zero.mp hcoord1).resolve_left (by positivity)
    have hdecomp := Problem97.CGN.orthonormal_pair_decomp (e := e) (n := n) he hn hen (x := v - w)
    have hzero : v - w = 0 := by
      simpa [hv0, hv1] using hdecomp
    exact sub_eq_zero.mp hzero
  have hF_equiv : ℝ² ≃ₗ[ℝ] ℝ² :=
    LinearEquiv.ofInjectiveOfFinrankEq F hF_inj (by simp)
  let M : ℝ² := midpoint ℝ q1 qm
  let T : ℝ² → ℝ² := fun z => F (z - M)
  have hTaff : ℝ² ≃ᵃ[ℝ] ℝ² := by
    simpa [T, F, Problem97.CGN.chordLinear, chordFrame, M] using
      (AffineEquiv.ofLinearEquiv hF_equiv M (0 : ℝ²))
  have hT : Function.Injective T := by
    intro x y hxy
    have hxy' : F (x - M) = F (y - M) := by
      simpa [T] using hxy
    have hxy'' : x - M = y - M := hF_inj hxy'
    simpa using hxy''
  have hnormF : ∀ v : ℝ², ‖F v‖ = scale * ‖v‖ := by
    intro v
    have hsq : ‖F v‖ ^ 2 = scale ^ 2 * ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [F, Problem97.CGN.chordLinear, chordFrame, Problem97.CGN.orthonormal_pair_normsq (e := e) (n := n) he hn hen,
        pow_two, mul_comm, mul_left_comm, mul_assoc, real_inner_comm]
      ring_nf
    have hnonneg : 0 ≤ scale * ‖v‖ := by positivity
    have hnormnonneg : 0 ≤ ‖F v‖ := norm_nonneg _
    nlinarith [hsq, hnonneg, hnormnonneg]
  have hareaF : ∀ u v : ℝ², stdOrientation.areaForm (F u) (F v) = scale ^ 2 * stdOrientation.areaForm u v := by
    intro u v
    have hFu : F u = vec2 (scale * ⟪u, e⟫_ℝ) (scale * ⟪u, n⟫_ℝ) := by
      ext i <;> fin_cases i <;>
        simp [F, Problem97.CGN.chordLinear, chordFrame, vec2, EuclideanSpace.single_apply]
    have hFv : F v = vec2 (scale * ⟪v, e⟫_ℝ) (scale * ⟪v, n⟫_ℝ) := by
      ext i <;> fin_cases i <;>
        simp [F, Problem97.CGN.chordLinear, chordFrame, vec2, EuclideanSpace.single_apply]
    have hvec_area :
        stdOrientation.areaForm
            (vec2 (scale * ⟪u, e⟫_ℝ) (scale * ⟪u, n⟫_ℝ))
            (vec2 (scale * ⟪v, e⟫_ℝ) (scale * ⟪v, n⟫_ℝ)) =
          scale ^ 2 * (⟪u, e⟫_ℝ * ⟪v, n⟫_ℝ - ⟪u, n⟫_ℝ * ⟪v, e⟫_ℝ) := by
      simpa using Problem97.CGN.vec2_areaForm_scaled (a := ⟪u, e⟫_ℝ) (b := ⟪u, n⟫_ℝ)
        (c := ⟪v, e⟫_ℝ) (d := ⟪v, n⟫_ℝ) scale
    calc
      stdOrientation.areaForm (F u) (F v)
          = stdOrientation.areaForm
              (vec2 (scale * ⟪u, e⟫_ℝ) (scale * ⟪u, n⟫_ℝ))
              (vec2 (scale * ⟪v, e⟫_ℝ) (scale * ⟪v, n⟫_ℝ)) := by
                  rw [hFu, hFv]
      _ = scale ^ 2 * (⟪u, e⟫_ℝ * ⟪v, n⟫_ℝ - ⟪u, n⟫_ℝ * ⟪v, e⟫_ℝ) := hvec_area
      _ = scale ^ 2 * stdOrientation.areaForm u v := by
          rw [Problem97.CGN.orthonormal_areaForm (e := e) he u v]
  have hdist_image : ∀ a b : ℝ², dist (T a) (T b) = scale * dist a b := by
    intro a b
    calc
      dist (T a) (T b) = ‖F (a - M) - F (b - M)‖ := by
        simp [T, dist_eq_norm]
      _ = ‖F ((a - M) - (b - M))‖ := by
        simpa using (congrArg (fun z : ℝ² => ‖z‖) (map_sub F (a - M) (b - M)).symm)
      _ = ‖F (a - b)‖ := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = scale * dist a b := by
        rw [hnormF, dist_eq_norm]
  have hdist_eq_iff : ∀ a b c : ℝ²,
      dist (T a) (T b) = dist (T a) (T c) ↔ dist a b = dist a c := by
    intro a b c
    constructor
    · intro h
      have hs : scale ≠ 0 := ne_of_gt hscale_pos
      rw [hdist_image a b, hdist_image a c] at h
      exact (mul_left_cancel₀ hs) h
    · intro h
      have hs : scale ≠ 0 := ne_of_gt hscale_pos
      rw [hdist_image a b, hdist_image a c]
      exact congrArg (fun x => scale * x) h
  have hconvexHull_mem_iff : ∀ {S : Set ℝ²} {a : ℝ²},
      T a ∈ convexHull ℝ (T '' S) ↔ a ∈ convexHull ℝ S := by
    intro S a
    let Taff : ℝ² →ᵃ[ℝ] ℝ² := AffineMap.mk' T F M (by
      intro p'
      simp [T, sub_eq_add_neg, map_add, map_sub, add_comm, add_left_comm, add_assoc])
    have hmap : T '' (convexHull ℝ S) = convexHull ℝ (T '' S) := by
      simpa [Taff] using (AffineMap.image_convexHull Taff S)
    constructor
    · intro ha
      have himage : T a ∈ T '' convexHull ℝ S := by
        rw [← hmap] at ha
        exact ha
      rcases himage with ⟨b, hb, hTb⟩
      have hba : b = a := hT hTb
      simpa [hba] using hb
    · intro ha
      simpa [hmap] using (show T a ∈ T '' convexHull ℝ S from ⟨a, ha, rfl⟩)
  have hhalfplane_sign : ∀ a b c : ℝ²,
      signedArea2 (T a) (T b) (T c) =
        (1 : ℝ) * (scale ^ 2) * signedArea2 a b c := by
    intro a b c
    have hsub1 : T b - T a = F (b - a) := by
      change F (b - M) - F (a - M) = F (b - a)
      rw [← map_sub]
      congr 1
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have hsub2 : T c - T a = F (c - a) := by
      change F (c - M) - F (a - M) = F (c - a)
      rw [← map_sub]
      congr 1
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    calc
      signedArea2 (T a) (T b) (T c)
          = stdOrientation.areaForm (T b - T a) (T c - T a) := by
              rw [signedArea2_eq_stdOrientation_areaForm]
      _ = stdOrientation.areaForm (F (b - a)) (F (c - a)) := by rw [hsub1, hsub2]
      _ = scale ^ 2 * stdOrientation.areaForm (b - a) (c - a) := hareaF _ _
      _ = (1 : ℝ) * (scale ^ 2) * signedArea2 a b c := by
            rw [signedArea2_eq_stdOrientation_areaForm]
            ring
  let hX : Fin m → ℝ := fun t => scale * ⟪L.points t - M, e⟫_ℝ
  let hY : Fin m → ℝ := fun t => scale * ⟪L.points t - M, n⟫_ℝ
  have hXdef : hX = fun t : Fin m => scale * ⟪L.points t - M, e⟫_ℝ := rfl
  have hYdef : hY = fun t : Fin m => scale * ⟪L.points t - M, n⟫_ℝ := rfl
  have hq1mid : q1 - M = -(1 / 2 : ℝ) • u := by
    calc
      q1 - M = (1 / 2 : ℝ) • (q1 - qm) := by
        simpa [M] using (left_sub_midpoint ℝ q1 qm)
      _ = -(1 / 2 : ℝ) • u := by
        rw [show q1 - qm = -u by simpa [u] using (neg_sub qm q1).symm]
        simp [smul_neg]
  have hqm_mid : qm - M = (1 / 2 : ℝ) • u := by
    simpa [M, u] using (right_sub_midpoint ℝ q1 qm)
  have hue : ⟪u, e⟫_ℝ = ‖u‖ := by
    dsimp [e]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    have hnorm : ‖u‖⁻¹ * ‖u‖ ^ 2 = ‖u‖ := by
      rw [pow_two]
      calc
        ‖u‖⁻¹ * (‖u‖ * ‖u‖) = (‖u‖⁻¹ * ‖u‖) * ‖u‖ := by ring
        _ = ‖u‖ := by
          rw [inv_mul_cancel₀ hu_norm.ne', one_mul]
    simpa [pow_two] using hnorm
  have hun : ⟪u, n⟫_ℝ = 0 := by
    have h0 : ‖u‖⁻¹ * ⟪u, n⟫_ℝ = 0 := by
      simpa [e, real_inner_smul_left] using hen
    have hne : ‖u‖⁻¹ ≠ 0 := by positivity
    exact (mul_eq_zero.mp h0).resolve_left hne
  have hcenter_x : scale * ⟪Packet.center - M, e⟫_ℝ = 0 := by
    have hdist_eq : dist Packet.center q1 = dist Packet.center qm := by
      simpa [q1, qm, dist_comm] using Packet.first_on_circle.trans Packet.last_on_circle.symm
    have hperp :
        Packet.center ∈ AffineSubspace.perpBisector q1 qm := by
      rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
      simpa [q1, qm] using hdist_eq
    have hperp' :
        ⟪Packet.center - midpoint ℝ q1 qm, qm - q1⟫_ℝ = 0 := by
      have h :=
        (AffineSubspace.mem_perpBisector_iff_inner_eq_zero
          (c := Packet.center) (p₁ := q1) (p₂ := qm)).mp hperp
      simpa [M] using h
    have heq : ⟪Packet.center - M, e⟫_ℝ = 0 := by
      have hs : ‖u‖ ≠ 0 := ne_of_gt hu_norm
      have hperp'' : ⟪Packet.center - M, u⟫_ℝ = 0 := by
        simpa [u, M] using hperp'
      have hmul : ‖u‖ * ⟪Packet.center - M, e⟫_ℝ = 0 := by
        rw [show e = ‖u‖⁻¹ • u by rfl, inner_smul_right]
        simpa [hperp'']
      exact (mul_eq_zero.mp hmul).resolve_left hs
    nlinarith [heq, hscale_pos]
  have hTcoord : ∀ z : ℝ²,
      T z = vec2 (scale * ⟪z - M, e⟫_ℝ) (scale * ⟪z - M, n⟫_ℝ) := by
    intro z
    ext i <;> fin_cases i <;>
      simp [T, F, Problem97.CGN.chordLinear, chordFrame, vec2, EuclideanSpace.single_apply, EuclideanSpace.ofLp_single]
  have hChordArea : ∀ z : ℝ²,
      signedArea2 (T q1) (T qm) (T z) = 2 * (scale * ⟪z - M, n⟫_ℝ) := by
    intro z
    have hTq1 : T q1 = vec2 (-1 : ℝ) 0 := by
      rw [hTcoord]
      have hq1e' : ⟪q1 - M, e⟫_ℝ = -(1 / 2 : ℝ) * ‖u‖ := by
        rw [hq1mid]
        simp [u, real_inner_smul_left, hue]
      have hq1e : scale * ⟪q1 - M, e⟫_ℝ = -1 := by
        calc
          scale * ⟪q1 - M, e⟫_ℝ = scale * (-(1 / 2 : ℝ) * ‖u‖) := by rw [hq1e']
          _ = -1 := by
            dsimp [scale]
            field_simp [hu_norm.ne']
      have hq1n : scale * ⟪q1 - M, n⟫_ℝ = 0 := by
        rw [hq1mid]
        simp [u, real_inner_smul_left, hun]
      simp [vec2, hq1e, hq1n]
    have hTqm : T qm = vec2 (1 : ℝ) 0 := by
      rw [hTcoord]
      have hqme' : ⟪qm - M, e⟫_ℝ = (1 / 2 : ℝ) * ‖u‖ := by
        rw [hqm_mid]
        simp [u, real_inner_smul_left, hue]
      have hqme : scale * ⟪qm - M, e⟫_ℝ = 1 := by
        calc
          scale * ⟪qm - M, e⟫_ℝ = scale * ((1 / 2 : ℝ) * ‖u‖) := by rw [hqme']
          _ = 1 := by
            dsimp [scale]
            field_simp [hu_norm.ne']
      have hqmn : scale * ⟪qm - M, n⟫_ℝ = 0 := by
        rw [hqm_mid]
        simp [u, real_inner_smul_left, hun]
      simp [vec2, hqme, hqmn]
    have hTz : T z = vec2 (scale * ⟪z - M, e⟫_ℝ) (scale * ⟪z - M, n⟫_ℝ) := hTcoord z
    have hvec :
        signedArea2 (vec2 (-1 : ℝ) 0) (vec2 (1 : ℝ) 0)
            (vec2 (scale * ⟪z - M, e⟫_ℝ) (scale * ⟪z - M, n⟫_ℝ)) =
          2 * (scale * ⟪z - M, n⟫_ℝ) := by
      norm_num [Problem97.signedArea2, vec2]
    rw [hTq1, hTqm, hTz]
    exact hvec
  have hcenter_y_nonpos : scale * ⟪Packet.center - M, n⟫_ℝ ≤ 0 := by
    have harea := hhalfplane_sign (a := q1) (b := qm) (c := Packet.center)
    have hchord := hChordArea Packet.center
    have hside : signedArea2 q1 qm Packet.center ≤ 0 := Hside.center_side_nonpos
    nlinarith [harea, hchord, hside, hscale_pos]
  have hXstrict : ∀ {i j : Fin m}, i < j → hX i < hX j := by
    intro i j hij
    have hproj := Hord.chord_projection_strict (i := i) (j := j) hij
    have hx : 0 < ⟪L.points j - L.points i, e⟫_ℝ := by
      have hu' : ⟪L.points j - L.points i, u⟫_ℝ > 0 := by
        simpa [u, q1, qm] using hproj
      have hmul : ‖u‖ * ⟪L.points j - L.points i, e⟫_ℝ = ⟪L.points j - L.points i, u⟫_ℝ := by
        simp [e, u, real_inner_smul_right, real_inner_self_eq_norm_sq, hu_norm.ne']
      nlinarith [hu', hmul, hu_norm]
    have hdiff : hX j - hX i = scale * ⟪L.points j - L.points i, e⟫_ℝ := by
      have hinner : ⟪L.points j + -M, e⟫_ℝ + -⟪L.points i + -M, e⟫_ℝ =
          ⟪L.points j + -L.points i, e⟫_ℝ := by
        have hj : ⟪L.points j + -M, e⟫_ℝ = ⟪L.points j, e⟫_ℝ - ⟪M, e⟫_ℝ := by
          simpa [sub_eq_add_neg] using (inner_sub_left (L.points j) M e)
        have hi : ⟪L.points i + -M, e⟫_ℝ = ⟪L.points i, e⟫_ℝ - ⟪M, e⟫_ℝ := by
          simpa [sub_eq_add_neg] using (inner_sub_left (L.points i) M e)
        have hji : ⟪L.points j + -L.points i, e⟫_ℝ = ⟪L.points j, e⟫_ℝ - ⟪L.points i, e⟫_ℝ := by
          simpa [sub_eq_add_neg] using (inner_sub_left (L.points j) (L.points i) e)
        rw [hj, hi, hji]
        ring
      have htmp1 : hX j - hX i = scale * (⟪L.points j + -M, e⟫_ℝ + -⟪L.points i + -M, e⟫_ℝ) := by
        simp [hX, sub_eq_add_neg]
        ring
      have htmp2 : scale * (⟪L.points j + -M, e⟫_ℝ + -⟪L.points i + -M, e⟫_ℝ) =
          scale * ⟪L.points j - L.points i, e⟫_ℝ := by
        rw [hinner]
        simp [sub_eq_add_neg]
      exact htmp1.trans htmp2
    nlinarith [hdiff, hx, hscale_pos]
  have hYnonneg : ∀ t : Fin m, 0 ≤ hY t := by
    intro t
    have hsa : 0 ≤ signedArea2 q1 qm (L.points t) := Hside.cap_side_nonneg t
    have hlink := hChordArea (L.points t)
    nlinarith [hsa, hlink, hhalfplane_sign (a := q1) (b := qm) (c := L.points t), hscale_pos]
  let tau : SimilarityTransportData T :=
    { scale := scale
      scale_pos := hscale_pos
      dist_image := hdist_image
      dist_eq_iff := hdist_eq_iff
      convexHull_mem_iff := hconvexHull_mem_iff
      orientation := (1 : ℝ)
      orientation_sq := by norm_num
      halfplane_sign := hhalfplane_sign }
  let coords : MinorCapChainCoords m :=
    { hm := Packet.hm
      X := hX
      Y := hY
      x_strict := by
        intro i j hij
        exact hXstrict hij
      X_first := by
        have hq1 : L.points (finIndex m 0 (by omega)) = q1 := by
          simp [q1, finIndex, firstIndex]
        calc
          hX (finIndex m 0 (by omega)) = scale * ⟪q1 - M, e⟫_ℝ := by
            simp [hX, hq1]
          _ = scale * (-(1 / 2 : ℝ) * ‖u‖) := by
            rw [hq1mid]
            simp [u, real_inner_smul_left, hue]
          _ = -1 := by
            dsimp [scale]
            field_simp [hu_norm.ne']
      X_last := by
        have hqm' : L.points (finIndex m (m - 1) (by omega)) = qm := by
          simp [qm, finIndex, lastIndex]
        calc
          hX (finIndex m (m - 1) (by omega)) = scale * ⟪qm - M, e⟫_ℝ := by
            simp [hX, hqm']
          _ = scale * ((1 / 2 : ℝ) * ‖u‖) := by
            rw [hqm_mid]
            simp [u, real_inner_smul_left, hue]
          _ = 1 := by
            dsimp [scale]
            field_simp [hu_norm.ne']
      Y_first := by
        have hq1 : L.points (finIndex m 0 (by omega)) = q1 := by
          simp [q1, finIndex, firstIndex]
        calc
          hY (finIndex m 0 (by omega)) = scale * ⟪q1 - M, n⟫_ℝ := by
            simp [hY, hq1]
          _ = 0 := by
            rw [hq1mid]
            simp [u, real_inner_smul_left, hun]
      Y_last := by
        have hqm' : L.points (finIndex m (m - 1) (by omega)) = qm := by
          simp [qm, finIndex, lastIndex]
        calc
          hY (finIndex m (m - 1) (by omega)) = scale * ⟪qm - M, n⟫_ℝ := by
            simp [hY, hqm']
          _ = 0 := by
            rw [hqm_mid]
            simp [u, real_inner_smul_left, hun]
      y_nonneg := by
        intro t
        simpa [hY] using hYnonneg t
      unit_disk := by
        intro t
        let lam : ℝ := -(scale * ⟪Packet.center - M, n⟫_ℝ)
        have hlam : 0 ≤ lam := by
          simpa [lam] using neg_nonneg.mpr hcenter_y_nonpos
        have hYt : 0 ≤ hY t := hYnonneg t
        have hTpt : T (L.points t) = vec2 (hX t) (hY t) := by
          rw [hXdef, hYdef]
          exact hTcoord (L.points t)
        have hTcenter : T Packet.center = vec2 0 (-lam) := by
          rw [hTcoord]
          ext i <;> fin_cases i <;> simp [lam, hcenter_x]
        have hTq1 : T q1 = vec2 (-1) 0 := by
          rw [hTcoord]
          have hq1e : scale * ⟪q1 - M, e⟫_ℝ = -1 := by
            have hq1e' : ⟪q1 - M, e⟫_ℝ = -(1 / 2 : ℝ) * ‖u‖ := by
              rw [hq1mid, real_inner_smul_left, hue]
            calc
              scale * ⟪q1 - M, e⟫_ℝ = scale * (-(1 / 2 : ℝ) * ‖u‖) := by rw [hq1e']
              _ = -1 := by
                dsimp [scale]
                field_simp [hu_norm.ne']
          have hq1n : scale * ⟪q1 - M, n⟫_ℝ = 0 := by
            rw [hq1mid, real_inner_smul_left, hun]
            ring
          simp [vec2, hq1e, hq1n]
        have hdist0 : dist (L.points t) Packet.center ≤ dist q1 Packet.center := by
          have h := Packet.disk_mem t
          rw [← Packet.first_on_circle] at h
          exact h
        have hdist_le : dist (T (L.points t)) (T Packet.center) ≤ dist (T q1) (T Packet.center) := by
          rw [hdist_image, hdist_image]
          exact mul_le_mul_of_nonneg_left hdist0 (le_of_lt hscale_pos)
        have hdist_sq : dist (T (L.points t)) (T Packet.center) ^ 2 ≤
            dist (T q1) (T Packet.center) ^ 2 := by
          have hdn1 : 0 ≤ dist (T (L.points t)) (T Packet.center) := dist_nonneg
          have hdn2 : 0 ≤ dist (T q1) (T Packet.center) := dist_nonneg
          have hle : |dist (T (L.points t)) (T Packet.center)| ≤
              |dist (T q1) (T Packet.center)| := by
            simpa [abs_of_nonneg hdn1, abs_of_nonneg hdn2] using hdist_le
          exact sq_le_sq.mpr hle
        have hleft : dist (T (L.points t)) (T Packet.center) ^ 2 =
            hX t ^ 2 + (hY t + lam) ^ 2 := by
          rw [hTpt, hTcenter]
          have h := Problem97.CGN.vec2_dist_sq (x1 := hX t) (y1 := hY t) (x2 := 0) (y2 := -lam)
          norm_num [sub_eq_add_neg] at h
          exact h
        have hright : dist (T q1) (T Packet.center) ^ 2 = 1 + lam ^ 2 := by
          have hq1e : scale * ⟪q1 - M, e⟫_ℝ = -1 := by
            have hq1e' : ⟪q1 - M, e⟫_ℝ = -(1 / 2 : ℝ) * ‖u‖ := by
              rw [hq1mid, real_inner_smul_left, hue]
            calc
              scale * ⟪q1 - M, e⟫_ℝ = scale * (-(1 / 2 : ℝ) * ‖u‖) := by rw [hq1e']
              _ = -1 := by
                dsimp [scale]
                field_simp [hu_norm.ne']
          have hq1n : scale * ⟪q1 - M, n⟫_ℝ = 0 := by
            rw [hq1mid, real_inner_smul_left, hun]
            ring
          have hq1coord : T q1 = vec2 (-1) 0 := by
            rw [hTcoord]
            simp [hq1e, hq1n]
          rw [hq1coord, hTcenter]
          have h := Problem97.CGN.vec2_dist_sq (x1 := -1) (y1 := (0 : ℝ)) (x2 := 0) (y2 := -lam)
          norm_num [sub_eq_add_neg] at h
          exact h
        have hsum : hX t ^ 2 + (hY t + lam) ^ 2 ≤ 1 + lam ^ 2 := by
          rw [hleft, hright] at hdist_sq
          exact hdist_sq
        have hcross : 0 ≤ 2 * hY t * lam := by
          have hprod : 0 ≤ hY t * lam := mul_nonneg hYt hlam
          have htwo : 0 ≤ (2 : ℝ) := by norm_num
          simpa [mul_assoc] using mul_nonneg htwo hprod
        have hsq : (hY t + lam) ^ 2 = hY t ^ 2 + 2 * hY t * lam + lam ^ 2 := by
          ring
        have hsum'' : hX t ^ 2 + hY t ^ 2 + 2 * hY t * lam + lam ^ 2 ≤ 1 + lam ^ 2 := by
          calc
            hX t ^ 2 + hY t ^ 2 + 2 * hY t * lam + lam ^ 2
                = hX t ^ 2 + (hY t + lam) ^ 2 := by ring
            _ ≤ 1 + lam ^ 2 := by
              exact hsum
        have hstep : hX t ^ 2 + hY t ^ 2 ≤ 1 := by
          linarith [hsum'', hcross]
        exact hstep
      adjacent_slopes_decreasing := by
        intro t ht
        have ht0 : t < m := by omega
        have ht1 : t + 1 < m := by omega
        have ht2 : t + 2 < m := ht
        have hx1 : 0 < hX (finIndex m (t + 1) ht1) - hX (finIndex m t ht0) := by
          have hltFin : finIndex m t ht0 < finIndex m (t + 1) ht1 := by
            simp [finIndex, Fin.lt_def]
          have hlt : hX (finIndex m t ht0) < hX (finIndex m (t + 1) ht1) := by
            exact hXstrict hltFin
          exact sub_pos.mpr hlt
        have hx2 : 0 < hX (finIndex m (t + 2) ht2) - hX (finIndex m (t + 1) ht1) := by
          have hltFin : finIndex m (t + 1) ht1 < finIndex m (t + 2) ht2 := by
            simp [finIndex, Fin.lt_def]
          have hlt : hX (finIndex m (t + 1) ht1) < hX (finIndex m (t + 2) ht2) := by
            exact hXstrict hltFin
          exact sub_pos.mpr hlt
        have hturn : signedArea2 (T (L.points (finIndex m t ht0)))
            (T (L.points (finIndex m (t + 1) ht1))) (T (L.points (finIndex m (t + 2) ht2))) ≤ 0 := by
          have horig : signedArea2 (L.points (finIndex m t ht0))
              (L.points (finIndex m (t + 1) ht1)) (L.points (finIndex m (t + 2) ht2)) ≤ 0 :=
            Hord.consecutive_turn_nonpos t ht
          have htrans := hhalfplane_sign (a := L.points (finIndex m t ht0))
            (b := L.points (finIndex m (t + 1) ht1))
            (c := L.points (finIndex m (t + 2) ht2))
          have hscale_sq_nonneg : 0 ≤ scale ^ 2 := sq_nonneg _
          rw [htrans]
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            mul_nonpos_of_nonneg_of_nonpos hscale_sq_nonneg horig
        have hturn' : signedArea2 (point hX hY (finIndex m t ht0))
            (point hX hY (finIndex m (t + 1) ht1)) (point hX hY (finIndex m (t + 2) ht2)) ≤ 0 := by
          have hturnvec :
              signedArea2 (vec2 (hX (finIndex m t ht0)) (hY (finIndex m t ht0)))
                (vec2 (hX (finIndex m (t + 1) ht1)) (hY (finIndex m (t + 1) ht1)))
                (vec2 (hX (finIndex m (t + 2) ht2)) (hY (finIndex m (t + 2) ht2))) ≤ 0 := by
            rw [hTcoord (L.points (finIndex m t ht0)),
              hTcoord (L.points (finIndex m (t + 1) ht1)),
              hTcoord (L.points (finIndex m (t + 2) ht2))] at hturn
            exact hturn
          rw [Problem97.CGN.point_eq_vec2 hX hY (finIndex m t ht0),
            Problem97.CGN.point_eq_vec2 hX hY (finIndex m (t + 1) ht1),
            Problem97.CGN.point_eq_vec2 hX hY (finIndex m (t + 2) ht2)]
          exact hturnvec
        have harea :
            signedArea2 (point hX hY (finIndex m t ht0))
              (point hX hY (finIndex m (t + 1) ht1))
              (point hX hY (finIndex m (t + 2) ht2)) =
              (hX (finIndex m (t + 1) ht1) - hX (finIndex m t ht0)) *
                (hY (finIndex m (t + 2) ht2) - hY (finIndex m (t + 1) ht1)) -
                (hY (finIndex m (t + 1) ht1) - hY (finIndex m t ht0)) *
                  (hX (finIndex m (t + 2) ht2) - hX (finIndex m (t + 1) ht1)) := by
          exact Problem97.CGN.point_signedArea2_eq (X := hX) (Y := hY) (finIndex m t ht0)
            (finIndex m (t + 1) ht1) (finIndex m (t + 2) ht2)
        have hcross :
            (hY (finIndex m (t + 2) ht2) - hY (finIndex m (t + 1) ht1)) *
                (hX (finIndex m (t + 1) ht1) - hX (finIndex m t ht0)) ≤
              (hY (finIndex m (t + 1) ht1) - hY (finIndex m t ht0)) *
                (hX (finIndex m (t + 2) ht2) - hX (finIndex m (t + 1) ht1)) := by
          have hturn'' := hturn'
          rw [harea] at hturn''
          have htemp :
              (hX (finIndex m (t + 1) ht1) - hX (finIndex m t ht0)) *
                  (hY (finIndex m (t + 2) ht2) - hY (finIndex m (t + 1) ht1)) ≤
                (hY (finIndex m (t + 1) ht1) - hY (finIndex m t ht0)) *
                  (hX (finIndex m (t + 2) ht2) - hX (finIndex m (t + 1) ht1)) := by
            exact sub_nonpos.mp hturn''
          rw [mul_comm]
          exact htemp
        have hratio :
            nextAdjacentSlope (X := hX) (Y := hY) t ht ≤
              adjacentSlope (X := hX) (Y := hY) t (by omega) := by
          rw [adjacentSlope, nextAdjacentSlope, slopeAt, slopeAt]
          exact (div_le_div_iff₀ hx2 hx1).2 hcross
        simpa [ge_iff_le] using hratio }
  refine ⟨T, hT, tau, ?_⟩
  exact ⟨⟨coords, by
    intro t
    have hpt : T (L.points t) = vec2 (hX t) (hY t) := by
      rw [hXdef, hYdef]
      exact hTcoord (L.points t)
    calc
      (L.map T hT).points t = T (L.points t) := rfl
      _ = vec2 (hX t) (hY t) := hpt
      _ = point hX hY t := by symm; exact Problem97.CGN.point_eq_vec2 hX hY t
  ⟩⟩

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN6
