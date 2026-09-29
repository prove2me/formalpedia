-- Prove2me | solution 1 for Problem97.boundaryCap_chordProjection_strict
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T05:51:08.322914+00:00
-- url     : https://prove2.me/submissions/692f4758-b2fa-48df-9b7a-3a69f32682d2

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.CGN.CGN4g:28518:55163. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_CGN_CGN
import Definitions.Def_Erdos9796Counting_CGN_CGN4g
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_SignedAreaOangle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Sort
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin

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

section Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN4g

open Problem97

/- Fragment from Erdos9796Proof.P97.CGN.CGN4g; source SHA-256 c412b95ca627805e0db3a1f0d192f80b93891249e4eb1369844d4f8206dcba79 -/


/-!
# CGN4g: ordered-cap block packaging

This file adds the closure-plan data carrier for the ordered-cap block cut out
of a global convex-boundary enumeration, together with the theorem wrappers
that are pure packaging.

The geometric producers for the block (`CGN4g1`, `CGN4g3`, `CGN4g4`) remain
separate. The declarations here are the sanctioned interfaces consumed by the
existing CGN6 / CGN7 layers.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace












variable {A C : Finset ℝ²}















































set_option maxHeartbeats 2000000 in
-- The boundary-cap projection normalization expands several basis-coordinate
-- identities and signed-area formulas in one theorem.

theorem solution
    {A C : Finset ℝ²} {n m : ℕ}
    {phi : Fin n → ℝ²} {L : Problem97.CGN.OrderedCap m}
    (_hA : Problem97.ConvexIndep A)
    (Block : Problem97.CGN.BoundaryCapBlock A C phi L)
    (hneg : ∀ {i j k : Fin n}, i < j → j < k →
      Problem97.signedArea2 (phi i) (phi j) (phi k) < 0)
    (Packet : Problem97.CGN.MecCapPacket A L)
    (Hside : Problem97.CGN.MinorCapSideHypotheses Packet) :
    ∀ {r s : Fin m}, r < s ->
      0 < inner ℝ (L.points s - L.points r)
        (L.points (Problem97.CGN.lastIndex Packet.hm) -
          L.points (Problem97.CGN.firstIndex Packet.hm)) := by
  have hhm : Packet.hm = Block.hm := Subsingleton.elim _ _
  let q1 : ℝ² := L.points (Problem97.CGN.firstIndex Block.hm)
  let qm : ℝ² := L.points (Problem97.CGN.lastIndex Block.hm)
  let u : ℝ² := qm - q1
  have hu : u ≠ 0 := by
    dsimp [u, q1, qm]
    exact sub_ne_zero.mpr <| by
      intro h
      have hidx : Problem97.CGN.firstIndex Block.hm = Problem97.CGN.lastIndex Block.hm :=
        L.injective h.symm
      have hval : (Problem97.CGN.firstIndex Block.hm).val =
          (Problem97.CGN.lastIndex Block.hm).val := congrArg Fin.val hidx
      have hval0 : (Problem97.CGN.firstIndex Block.hm).val = 0 := by
        simp [Problem97.CGN.firstIndex]
      have hval1 : (Problem97.CGN.lastIndex Block.hm).val = m - 1 := by
        simp [Problem97.CGN.lastIndex]
      rw [hval0, hval1] at hval
      have hm : 2 ≤ m := Block.hm
      omega
  let nvec : ℝ² := Problem97.stdOrientation.rightAngleRotation u
  let β := Problem97.stdOrientation.basisRightAngleRotation u hu
  let M : ℝ² := midpoint ℝ q1 qm
  let X : Fin m → ℝ := fun t => β.repr (L.points t - M) 0
  let Y : Fin m → ℝ := fun t => β.repr (L.points t - M) 1
  let xc : ℝ := β.repr (Packet.center - M) 0
  let yc : ℝ := β.repr (Packet.center - M) 1
  have hsum_pt : ∀ t : Fin m, L.points t - M = X t • u + Y t • nvec := by
    intro t
    simpa [β, X, Y, nvec] using (β.sum_repr (L.points t - M)).symm
  have hsum_center : Packet.center - M = xc • u + yc • nvec := by
    simpa [β, xc, yc, nvec] using (β.sum_repr (Packet.center - M)).symm
  have hnorm_nvec : ‖nvec‖ = ‖u‖ := by
    simpa [nvec] using Problem97.stdOrientation.rightAngleRotation.norm_map u
  have hβu : β.repr u = Finsupp.single 0 (1 : ℝ) := by
    simpa [β, nvec] using (β.repr_self 0)
  have hβu0 : β.repr u 0 = 1 := by
    simp [hβu]
  have hβu1 : β.repr u 1 = 0 := by
    simp [hβu]
  have horth : inner ℝ u nvec = 0 := by
    simpa [nvec] using
      Problem97.stdOrientation.inner_rightAngleRotation_self u
  have horth_rev : inner ℝ nvec u = 0 := by
    simpa [real_inner_comm] using horth
  have harea_u_left : ∀ r : ℝ, Problem97.stdOrientation.areaForm u (r • u) = 0 := by
    intro r
    rw [map_smul]
    simp
  have harea_u_right : ∀ r : ℝ,
      Problem97.stdOrientation.areaForm u (r • nvec) = r * ‖u‖ ^ 2 := by
    intro r
    rw [map_smul]
    simp [nvec, Orientation.areaForm_rightAngleRotation_right]
  have harea_swap : Problem97.stdOrientation.areaForm nvec u = -‖u‖ ^ 2 := by
    have h :=
      Problem97.stdOrientation.areaForm_rightAngleRotation_right (x := u) (y := u)
    rw [Problem97.stdOrientation.areaForm_swap] at h
    simpa [nvec] using h
  have hsqpos : 0 < ‖u‖ ^ 2 := by
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
  have hq1mid : q1 - M = (-(1 / 2 : ℝ)) • u := by
    calc
      q1 - M = (1 / 2 : ℝ) • (q1 - qm) := by
        simpa [M] using (left_sub_midpoint ℝ q1 qm)
      _ = (-(1 / 2 : ℝ)) • u := by
        rw [show q1 - qm = -u by
          dsimp [u]
          abel_nf]
        simp [smul_neg]
  have hqm_mid : qm - M = (1 / 2 : ℝ) • u := by
    simpa [M, u] using (right_sub_midpoint ℝ q1 qm)
  have hX_first : X (Problem97.CGN.firstIndex Block.hm) = -(1 / 2 : ℝ) := by
    have h := congrArg (fun v : ℝ² => β.repr v 0) hq1mid
    change X (Problem97.CGN.firstIndex Block.hm) =
      (β.repr ((-(1 / 2 : ℝ)) • u)) 0 at h
    rw [map_smul, hβu] at h
    simpa using h
  have hY_first : Y (Problem97.CGN.firstIndex Block.hm) = 0 := by
    have h := congrArg (fun v : ℝ² => β.repr v 1) hq1mid
    change Y (Problem97.CGN.firstIndex Block.hm) =
      (β.repr ((-(1 / 2 : ℝ)) • u)) 1 at h
    rw [map_smul, hβu] at h
    simpa using h
  have hX_last : X (Problem97.CGN.lastIndex Block.hm) = (1 / 2 : ℝ) := by
    have h := congrArg (fun v : ℝ² => β.repr v 0) hqm_mid
    change X (Problem97.CGN.lastIndex Block.hm) =
      (β.repr ((1 / 2 : ℝ) • u)) 0 at h
    rw [map_smul, hβu] at h
    simpa using h
  have hY_last : Y (Problem97.CGN.lastIndex Block.hm) = 0 := by
    have h := congrArg (fun v : ℝ² => β.repr v 1) hqm_mid
    change Y (Problem97.CGN.lastIndex Block.hm) =
      (β.repr ((1 / 2 : ℝ) • u)) 1 at h
    rw [map_smul, hβu] at h
    simpa using h
  have hcenter_perp : inner ℝ (Packet.center - M) u = 0 := by
    have hdist_eq : dist Packet.center q1 = dist Packet.center qm := by
      simpa [q1, qm, dist_comm] using
        Packet.first_on_circle.trans Packet.last_on_circle.symm
    have hperp : Packet.center ∈ AffineSubspace.perpBisector q1 qm := by
      rw [AffineSubspace.mem_perpBisector_iff_dist_eq]
      simpa using hdist_eq
    have h :=
      (AffineSubspace.mem_perpBisector_iff_inner_eq_zero
        (c := Packet.center) (p₁ := q1) (p₂ := qm)).mp hperp
    simpa [M] using h
  have hxc_zero : xc = 0 := by
    have hinner : inner ℝ (Packet.center - M) u = xc * ‖u‖ ^ 2 := by
      have horth' : inner ℝ nvec u = 0 := by
        simpa [real_inner_comm] using horth
      calc
        inner ℝ (Packet.center - M) u = inner ℝ (xc • u + yc • nvec) u := by
          rw [hsum_center]
        _ = inner ℝ (xc • u) u + inner ℝ (yc • nvec) u := by
          rw [inner_add_left]
        _ = xc * ‖u‖ ^ 2 + yc * 0 := by
          rw [inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq, horth']
          simp
        _ = xc * ‖u‖ ^ 2 := by ring
    nlinarith [hcenter_perp, hinner, hsqpos]
  have hcenter_decomp : Packet.center - M = yc • nvec := by
    rw [hsum_center, hxc_zero, zero_smul, zero_add]
  have hdist_sq_coeff :
      ∀ a b : ℝ, ‖a • u + b • nvec‖ ^ 2 = (a ^ 2 + b ^ 2) * ‖u‖ ^ 2 := by
    intro a b
    have horth' : inner ℝ (a • u) (b • nvec) = 0 := by
      rw [inner_smul_left, inner_smul_right, horth]
      ring
    have hnorm :
        ‖a • u + b • nvec‖ ^ 2 = ‖a • u‖ ^ 2 + ‖b • nvec‖ ^ 2 := by
      simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (a • u) (b • nvec) horth'
    have hu_part : ‖a • u‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 := by
      calc
        ‖a • u‖ ^ 2 = (|a| * ‖u‖) ^ 2 := by rw [norm_smul, Real.norm_eq_abs]
        _ = |a| ^ 2 * ‖u‖ ^ 2 := by ring
        _ = a ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]
    have hn_part : ‖b • nvec‖ ^ 2 = b ^ 2 * ‖u‖ ^ 2 := by
      calc
        ‖b • nvec‖ ^ 2 = (|b| * ‖u‖) ^ 2 := by rw [norm_smul, Real.norm_eq_abs, hnorm_nvec]
        _ = |b| ^ 2 * ‖u‖ ^ 2 := by ring
        _ = b ^ 2 * ‖u‖ ^ 2 := by rw [sq_abs]
    rw [hnorm, hu_part, hn_part]
    ring
  have hpt_minus_q1 : ∀ t : Fin m,
      L.points t - q1 = (X t + 1 / 2) • u + Y t • nvec := by
    intro t
    calc
      L.points t - q1 = (L.points t - M) - (q1 - M) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
        abel_nf
      _ = (X t • u + Y t • nvec) - ((-(1 / 2 : ℝ)) • u) := by
        rw [hsum_pt t, hq1mid]
      _ = (X t • u + (1 / 2 : ℝ) • u) + Y t • nvec := by
        rw [sub_eq_add_neg, neg_smul]
        abel_nf
      _ = (X t + 1 / 2) • u + Y t • nvec := by
        rw [← add_smul]
  have hqm_minus_pt : ∀ t : Fin m,
      qm - L.points t = (1 / 2 - X t) • u + (-Y t) • nvec := by
    intro t
    calc
      qm - L.points t = (qm - M) - (L.points t - M) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
        abel_nf
      _ = ((1 / 2 : ℝ) • u) - (X t • u + Y t • nvec) := by
        rw [hqm_mid, hsum_pt t]
      _ = ((1 / 2 : ℝ) • u + (-X t) • u) + (-Y t) • nvec := by
        rw [sub_eq_add_neg, neg_smul, neg_smul]
        abel_nf
      _ = (1 / 2 - X t) • u + (-Y t) • nvec := by
        rw [← add_smul]
        simp [sub_eq_add_neg]
  have hpt_minus_center : ∀ t : Fin m,
      L.points t - Packet.center = X t • u + (Y t - yc) • nvec := by
    intro t
    calc
      L.points t - Packet.center = (L.points t - M) - (Packet.center - M) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
        abel_nf
      _ = (X t • u + Y t • nvec) - (yc • nvec) := by
        rw [hsum_pt t, hcenter_decomp]
      _ = X t • u + (Y t • nvec + -(yc • nvec)) := by
        rw [sub_eq_add_neg]
        abel_nf
      _ = X t • u + (Y t • nvec + (-yc) • nvec) := by
        rw [neg_smul]
      _ = X t • u + (Y t - yc) • nvec := by
        rw [← add_smul]
        simp [sub_eq_add_neg]
  have hq1_minus_center :
      q1 - Packet.center = (-(1 / 2 : ℝ)) • u + (-yc) • nvec := by
    calc
      q1 - Packet.center = (q1 - M) - (Packet.center - M) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
        abel_nf
      _ = ((-(1 / 2 : ℝ)) • u) - (yc • nvec) := by
        rw [hq1mid, hcenter_decomp]
      _ = (-(1 / 2 : ℝ)) • u + (-yc) • nvec := by
        simpa [sub_eq_add_neg, neg_smul]
  have hdiff_coords : ∀ r s : Fin m,
      L.points s - L.points r = (X s - X r) • u + (Y s - Y r) • nvec := by
    intro r s
    calc
      L.points s - L.points r = (L.points s - M) - (L.points r - M) := by
        rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
        abel_nf
      _ = (X s • u + Y s • nvec) - (X r • u + Y r • nvec) := by
        rw [hsum_pt s, hsum_pt r]
      _ = (X s • u + (-X r) • u) + (Y s • nvec + (-Y r) • nvec) := by
        rw [sub_eq_add_neg, neg_smul, neg_smul]
        abel_nf
      _ = (X s - X r) • u + (Y s - Y r) • nvec := by
        rw [← add_smul, ← add_smul]
        simp [sub_eq_add_neg]
  have harea_first_last : ∀ t : Fin m,
      Problem97.signedArea2 q1 qm (L.points t) = Y t * ‖u‖ ^ 2 := by
    intro t
    calc
      Problem97.signedArea2 q1 qm (L.points t) =
          Problem97.stdOrientation.areaForm u (L.points t - q1) := by
        rw [Problem97.signedArea2_eq_stdOrientation_areaForm]
      _ = Problem97.stdOrientation.areaForm u
          ((X t + 1 / 2) • u + Y t • nvec) := by
        rw [hpt_minus_q1 t]
      _ = Y t * ‖u‖ ^ 2 := by
        rw [map_add, harea_u_left (X t + 1 / 2), harea_u_right (Y t)]
        simp
  have harea_first_t_last : ∀ t : Fin m,
      Problem97.signedArea2 q1 (L.points t) qm = -Y t * ‖u‖ ^ 2 := by
    intro t
    calc
      Problem97.signedArea2 q1 (L.points t) qm =
          Problem97.stdOrientation.areaForm (L.points t - q1) (qm - q1) := by
        rw [Problem97.signedArea2_eq_stdOrientation_areaForm]
      _ = Problem97.stdOrientation.areaForm
          ((X t + 1 / 2) • u + Y t • nvec) u := by
        rw [hpt_minus_q1 t]
      _ = -Y t * ‖u‖ ^ 2 := by
        simp [map_add, map_smul, harea_swap]
  have harea_first_rs : ∀ r s : Fin m,
      Problem97.signedArea2 q1 (L.points r) (L.points s) =
        ((X r + 1 / 2) * Y s - Y r * (X s + 1 / 2)) * ‖u‖ ^ 2 := by
    intro r s
    calc
      Problem97.signedArea2 q1 (L.points r) (L.points s) =
          Problem97.stdOrientation.areaForm (L.points r - q1) (L.points s - q1) := by
        rw [Problem97.signedArea2_eq_stdOrientation_areaForm]
      _ = Problem97.stdOrientation.areaForm
          ((X r + 1 / 2) • u + Y r • nvec)
          ((X s + 1 / 2) • u + Y s • nvec) := by
        rw [hpt_minus_q1 r, hpt_minus_q1 s]
      _ = ((X r + 1 / 2) * Y s - Y r * (X s + 1 / 2)) * ‖u‖ ^ 2 := by
        have hun : Problem97.stdOrientation.areaForm u nvec = ‖u‖ ^ 2 := by
          simpa using harea_u_right (1 : ℝ)
        simp [map_add, map_smul, hun, harea_swap]
        ring_nf
  have harea_rs_last : ∀ r s : Fin m,
      Problem97.signedArea2 (L.points r) (L.points s) qm =
        ((X r - 1 / 2) * Y s - (X s - 1 / 2) * Y r) * ‖u‖ ^ 2 := by
    intro r s
    calc
      Problem97.signedArea2 (L.points r) (L.points s) qm =
          Problem97.stdOrientation.areaForm
            (L.points s - L.points r) (qm - L.points r) := by
        rw [Problem97.signedArea2_eq_stdOrientation_areaForm]
      _ = Problem97.stdOrientation.areaForm
          ((X s - X r) • u + (Y s - Y r) • nvec)
          ((1 / 2 - X r) • u + (-Y r) • nvec) := by
        rw [hdiff_coords r s, hqm_minus_pt r]
      _ = ((X r - 1 / 2) * Y s - (X s - 1 / 2) * Y r) * ‖u‖ ^ 2 := by
        have hun : Problem97.stdOrientation.areaForm u nvec = ‖u‖ ^ 2 := by
          simpa using harea_u_right (1 : ℝ)
        simp [map_add, map_smul, hun, harea_swap]
        ring_nf
  have hcenter_side_coeff : yc ≤ 0 := by
    have hside : Problem97.signedArea2 q1 qm Packet.center ≤ 0 := by
      simpa [q1, qm] using Hside.center_side_nonpos
    have harea_center :
        Problem97.signedArea2 q1 qm Packet.center = yc * ‖u‖ ^ 2 := by
      calc
        Problem97.signedArea2 q1 qm Packet.center =
            Problem97.stdOrientation.areaForm u (Packet.center - q1) := by
          rw [Problem97.signedArea2_eq_stdOrientation_areaForm]
        _ = Problem97.stdOrientation.areaForm u
            (((1 / 2 : ℝ)) • u + yc • nvec) := by
          have h : Packet.center - q1 = ((1 / 2 : ℝ)) • u + yc • nvec := by
            calc
              Packet.center - q1 = (Packet.center - M) - (q1 - M) := by
                rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg]
                abel_nf
              _ = (yc • nvec) - ((-(1 / 2 : ℝ)) • u) := by
                rw [hcenter_decomp, hq1mid]
              _ = ((1 / 2 : ℝ)) • u + yc • nvec := by
                rw [sub_eq_add_neg, neg_smul]
                abel_nf
          rw [h]
        _ = yc * ‖u‖ ^ 2 := by
          rw [map_add, harea_u_left (1 / 2), harea_u_right yc]
          simp
    nlinarith [hside, harea_center, hsqpos]
  have hY_nonneg : ∀ t : Fin m, 0 ≤ Y t := by
    intro t
    have hside : 0 ≤ Problem97.signedArea2 q1 qm (L.points t) := by
      simpa [q1, qm] using Hside.cap_side_nonneg t
    rw [harea_first_last t] at hside
    nlinarith [hside, hsqpos]
  have hdisk_bound : ∀ t : Fin m,
      X t ^ 2 + (Y t - yc) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 + yc ^ 2 := by
    intro t
    have hdist : dist (L.points t) Packet.center ≤ dist q1 Packet.center := by
      have hdisk : dist (L.points t) Packet.center ≤ Packet.radius := Packet.disk_mem t
      have hq1rad : dist q1 Packet.center = Packet.radius := by
        simpa [q1, hhm] using Packet.first_on_circle
      rw [hq1rad]
      exact hdisk
    have hdist_sq : dist (L.points t) Packet.center ^ 2 ≤ dist q1 Packet.center ^ 2 := by
      have hdist_left_nonneg : 0 ≤ dist (L.points t) Packet.center := dist_nonneg
      have hdist_right_nonneg : 0 ≤ dist q1 Packet.center := dist_nonneg
      nlinarith [hdist, hdist_left_nonneg, hdist_right_nonneg]
    have hleft :
        dist (L.points t) Packet.center ^ 2 =
          (X t ^ 2 + (Y t - yc) ^ 2) * ‖u‖ ^ 2 := by
      rw [dist_eq_norm]
      rw [hpt_minus_center t, hdist_sq_coeff]
    have hright :
        dist q1 Packet.center ^ 2 = ((1 / 2 : ℝ) ^ 2 + yc ^ 2) * ‖u‖ ^ 2 := by
      rw [dist_eq_norm]
      rw [hq1_minus_center, hdist_sq_coeff]
      ring_nf
    rw [hleft, hright] at hdist_sq
    nlinarith [hdist_sq, hsqpos]
  have hX_sq_bound : ∀ t : Fin m, X t ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    intro t
    have hbound := hdisk_bound t
    have hy : 0 ≤ Y t := hY_nonneg t
    nlinarith [hbound, hy, hcenter_side_coeff]
  have hX_lo : ∀ t : Fin m, -(1 / 2 : ℝ) ≤ X t := by
    intro t
    have hsq := hX_sq_bound t
    nlinarith
  have hX_hi : ∀ t : Fin m, X t ≤ (1 / 2 : ℝ) := by
    intro t
    have hsq := hX_sq_bound t
    nlinarith
  have hX_eq_first : ∀ {t : Fin m}, X t = -(1 / 2 : ℝ) → t = Problem97.CGN.firstIndex Block.hm := by
    intro t hxt
    have hbound := hdisk_bound t
    have hy : 0 ≤ Y t := hY_nonneg t
    have hyc0 : 2 * yc ≤ 0 := by
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_nonpos_of_nonneg_of_nonpos htwo hcenter_side_coeff
    have hyc : 0 ≤ Y t - 2 * yc := by
      exact sub_nonneg.mpr (le_trans hyc0 hy)
    rw [hxt] at hbound
    norm_num at hbound
    have hyzero : Y t = 0 := by
      have hsq_le : (Y t - yc) ^ 2 ≤ yc ^ 2 := hbound
      have hprod_le : Y t * (Y t - 2 * yc) ≤ 0 := by
        rw [show Y t * (Y t - 2 * yc) = (Y t - yc) ^ 2 - yc ^ 2 by ring]
        exact sub_nonpos.mpr hsq_le
      have hprod_nonneg : 0 ≤ Y t * (Y t - 2 * yc) := by
        exact mul_nonneg hy hyc
      have hprod_zero : Y t * (Y t - 2 * yc) = 0 := le_antisymm hprod_le hprod_nonneg
      rcases mul_eq_zero.mp hprod_zero with hY | hyc0
      · exact hY
      · linarith [hy, hcenter_side_coeff, hyc0]
    have hvec : L.points t - M = q1 - M := by
      rw [hsum_pt t, hq1mid, hxt, hyzero]
      simp
    have hpt : L.points t = q1 := by
      exact sub_left_injective hvec
    exact L.injective hpt
  have hX_eq_last : ∀ {t : Fin m}, X t = (1 / 2 : ℝ) → t = Problem97.CGN.lastIndex Block.hm := by
    intro t hxt
    have hbound := hdisk_bound t
    have hy : 0 ≤ Y t := hY_nonneg t
    have hyc0 : 2 * yc ≤ 0 := by
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_nonpos_of_nonneg_of_nonpos htwo hcenter_side_coeff
    have hyc : 0 ≤ Y t - 2 * yc := by
      exact sub_nonneg.mpr (le_trans hyc0 hy)
    rw [hxt] at hbound
    norm_num at hbound
    have hyzero : Y t = 0 := by
      have hsq_le : (Y t - yc) ^ 2 ≤ yc ^ 2 := hbound
      have hprod_le : Y t * (Y t - 2 * yc) ≤ 0 := by
        rw [show Y t * (Y t - 2 * yc) = (Y t - yc) ^ 2 - yc ^ 2 by ring]
        exact sub_nonpos.mpr hsq_le
      have hprod_nonneg : 0 ≤ Y t * (Y t - 2 * yc) := by
        exact mul_nonneg hy hyc
      have hprod_zero : Y t * (Y t - 2 * yc) = 0 := le_antisymm hprod_le hprod_nonneg
      rcases mul_eq_zero.mp hprod_zero with hY | hyc0
      · exact hY
      · linarith [hy, hcenter_side_coeff, hyc0]
    have hvec : L.points t - M = qm - M := by
      rw [hsum_pt t, hqm_mid, hxt, hyzero]
      simp
    have hpt : L.points t = qm := by
      exact sub_left_injective hvec
    exact L.injective hpt
  have hfirst_lt_of_ne : ∀ {t : Fin m}, t ≠ Problem97.CGN.firstIndex Block.hm →
      Problem97.CGN.firstIndex Block.hm < t := by
    intro t ht
    change 0 < t.val
    have hne0 : t.val ≠ 0 := by
      intro hzero
      apply ht
      apply Fin.ext
      simpa [Problem97.CGN.firstIndex] using hzero
    exact Nat.pos_iff_ne_zero.mpr hne0
  have hlt_last_of_ne : ∀ {t : Fin m}, t ≠ Problem97.CGN.lastIndex Block.hm →
      t < Problem97.CGN.lastIndex Block.hm := by
    intro t ht
    change t.val < m - 1
    have hne_last : t.val ≠ m - 1 := by
      intro hz
      apply ht
      apply Fin.ext
      simpa [Problem97.CGN.lastIndex] using hz
    omega
  have hX_gt_first : ∀ {t : Fin m}, t ≠ Problem97.CGN.firstIndex Block.hm →
      -(1 / 2 : ℝ) < X t := by
    intro t ht
    have hlo := hX_lo t
    have hneq : X t ≠ -(1 / 2 : ℝ) := by
      intro h
      exact ht (hX_eq_first h)
    exact lt_of_le_of_ne hlo hneq.symm
  have hX_lt_last : ∀ {t : Fin m}, t ≠ Problem97.CGN.lastIndex Block.hm →
      X t < (1 / 2 : ℝ) := by
    intro t ht
    have hhi := hX_hi t
    have hneq : X t ≠ (1 / 2 : ℝ) := by
      intro h
      exact ht (hX_eq_last h)
    exact lt_of_le_of_ne hhi hneq
  have hY_pos_interior : ∀ {t : Fin m},
      Problem97.CGN.firstIndex Block.hm < t →
      t < Problem97.CGN.lastIndex Block.hm →
      0 < Y t := by
    intro t hfirst hlast
    have hidx_first : Block.idx (Problem97.CGN.firstIndex Block.hm) < Block.idx t := by
      simpa [Block.idx_first] using Block.idx_strict hfirst
    have hidx_last : Block.idx t < Block.idx (Problem97.CGN.lastIndex Block.hm) := by
      simpa [Block.idx_last] using Block.idx_strict hlast
    have hq1_phi : q1 = phi (Block.idx (Problem97.CGN.firstIndex Block.hm)) := by
      simp [q1, Block.points_eq]
    have hqm_phi : qm = phi (Block.idx (Problem97.CGN.lastIndex Block.hm)) := by
      simp [qm, Block.points_eq]
    have ht_phi : L.points t = phi (Block.idx t) := by
      simpa using Block.points_eq t
    have hneg_t : Problem97.signedArea2 q1 (L.points t) qm < 0 := by
      rw [hq1_phi, ht_phi, hqm_phi]
      exact hneg hidx_first hidx_last
    rw [harea_first_t_last t] at hneg_t
    by_contra hy_not
    have hy_nonpos : Y t ≤ 0 := le_of_not_gt hy_not
    have hnegY_nonneg : 0 ≤ -Y t := by
      exact neg_nonneg.mpr hy_nonpos
    have hprod_nonneg : 0 ≤ (-Y t) * ‖u‖ ^ 2 := by
      exact mul_nonneg hnegY_nonneg (le_of_lt hsqpos)
    exact not_lt_of_ge hprod_nonneg hneg_t
  have hproj_formula : ∀ r s : Fin m,
      inner ℝ (L.points s - L.points r) (qm - q1) =
        (X s - X r) * ‖u‖ ^ 2 := by
    intro r s
    calc
      inner ℝ (L.points s - L.points r) (qm - q1) = inner ℝ (L.points s - L.points r) u := by
        simp [u, qm, q1]
      _ = inner ℝ ((X s - X r) • u + (Y s - Y r) • nvec) u := by rw [hdiff_coords r s]
      _ = (X s - X r) * ‖u‖ ^ 2 := by
        have horth2 : inner ℝ ((Y s - Y r) • nvec) u = 0 := by
          rw [inner_smul_left, horth_rev]
          simp
        calc
          inner ℝ ((X s - X r) • u + (Y s - Y r) • nvec) u =
              (starRingEnd ℝ (X s - X r)) * ‖u‖ ^ 2 + 0 := by
            rw [inner_add_left, horth2, inner_smul_left, real_inner_self_eq_norm_sq]
          _ = (X s - X r) * ‖u‖ ^ 2 := by
            simp
  have hproj_formula' : ∀ r s : Fin m,
      inner ℝ (L.points s - L.points r)
        (L.points (Problem97.CGN.lastIndex Packet.hm) -
          L.points (Problem97.CGN.firstIndex Packet.hm)) =
        (X s - X r) * ‖u‖ ^ 2 := by
    intro r s
    simpa [q1, qm, hhm] using hproj_formula r s
  intro r s hrs
  by_cases hr_first : r = Problem97.CGN.firstIndex Block.hm
  · subst hr_first
    have hs_ne : s ≠ Problem97.CGN.firstIndex Block.hm := ne_of_gt hrs
    have hXs : -(1 / 2 : ℝ) < X s := hX_gt_first hs_ne
    have hproj := hproj_formula' (Problem97.CGN.firstIndex Block.hm) s
    rw [hX_first] at hproj
    nlinarith [hproj, hsqpos, hXs]
  · by_cases hs_last : s = Problem97.CGN.lastIndex Block.hm
    · subst hs_last
      have hr_ne : r ≠ Problem97.CGN.lastIndex Block.hm := ne_of_lt hrs
      have hXr : X r < (1 / 2 : ℝ) := hX_lt_last hr_ne
      have hproj := hproj_formula' r (Problem97.CGN.lastIndex Block.hm)
      rw [hX_last] at hproj
      nlinarith [hproj, hsqpos, hXr]
    · have hr_int : Problem97.CGN.firstIndex Block.hm < r := hfirst_lt_of_ne hr_first
      have hs_int : s < Problem97.CGN.lastIndex Block.hm := hlt_last_of_ne hs_last
      have hs_from_first : Problem97.CGN.firstIndex Block.hm < s := lt_trans hr_int hrs
      have hr_to_last : r < Problem97.CGN.lastIndex Block.hm := lt_trans hrs hs_int
      have hYr : 0 < Y r := hY_pos_interior hr_int hr_to_last
      have hYs : 0 < Y s := hY_pos_interior hs_from_first hs_int
      have hXr_lo : 0 < X r + 1 / 2 := by
        have h := hX_gt_first hr_first
        linarith
      have hXs_lo : 0 < X s + 1 / 2 := by
        have h := hX_gt_first (by
          intro hs0
          exact hs_from_first.ne hs0.symm)
        linarith
      have hXr_hi : 0 < 1 / 2 - X r := by
        have h := hX_lt_last (by
          intro hr0
          exact hr_to_last.ne hr0)
        linarith
      have hXs_hi : 0 < 1 / 2 - X s := by
        have h := hX_lt_last hs_last
        linarith
      have hidx_first_r : Block.idx (Problem97.CGN.firstIndex Block.hm) < Block.idx r := by
        simpa [Block.idx_first] using Block.idx_strict hr_int
      have hidx_r_s : Block.idx r < Block.idx s := Block.idx_strict hrs
      have hidx_s_last : Block.idx s < Block.idx (Problem97.CGN.lastIndex Block.hm) := by
        simpa [Block.idx_last] using Block.idx_strict hs_int
      have hneg_left : Problem97.signedArea2 q1 (L.points r) (L.points s) < 0 := by
        simpa [q1, qm, Block.points_eq, Block.idx_first, Block.idx_last] using
          hneg hidx_first_r hidx_r_s
      have hneg_right : Problem97.signedArea2 (L.points r) (L.points s) qm < 0 := by
        simpa [q1, qm, Block.points_eq, Block.idx_first, Block.idx_last] using
          hneg hidx_r_s hidx_s_last
      have hineq_left :
          (X r + 1 / 2) * Y s < Y r * (X s + 1 / 2) := by
        rw [harea_first_rs r s] at hneg_left
        nlinarith [hneg_left, hsqpos]
      have hineq_right :
          Y r / Y s < (1 / 2 - X r) / (1 / 2 - X s) := by
        have htmp :
            (1 / 2 - X s) * Y r < (1 / 2 - X r) * Y s := by
          rw [harea_rs_last r s] at hneg_right
          nlinarith [hneg_right, hsqpos]
        exact (div_lt_div_iff₀ hYs hXs_hi).2 <| by
          simpa [mul_comm, mul_left_comm, mul_assoc] using htmp
      have hineq_left' :
          (X r + 1 / 2) / (X s + 1 / 2) < Y r / Y s := by
        exact (div_lt_div_iff₀ hXs_lo hYs).2 <| by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hineq_left
      have hratio :
          (X r + 1 / 2) / (X s + 1 / 2) < (1 / 2 - X r) / (1 / 2 - X s) :=
        lt_trans hineq_left' hineq_right
      have hcross :
          (X r + 1 / 2) * (1 / 2 - X s) < (1 / 2 - X r) * (X s + 1 / 2) := by
        exact (div_lt_div_iff₀ hXs_lo hXs_hi).1 hratio
      have hXrs : X r < X s := by
        nlinarith [hcross]
      have hproj := hproj_formula' r s
      nlinarith [hproj, hsqpos, hXrs]

end Erdos9796CountingFragment_Erdos9796Proof_P97_CGN_CGN4g
