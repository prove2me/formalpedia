-- Prove2me | solution 1 for RelaxationMethod.LowDim.axisSphere_eq
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:52:57.954974+00:00
-- url     : https://prove2.me/submissions/dbd561bc-1185-4a71-b1d9-3910b3bde69a

import Definitions.Def_RelaxationMethod_LowDim_AxisSphere
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Geometry.Euclidean.PerpBisector
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
set_option autoImplicit false
open RelaxationMethod.LowDim EuclideanGeometry
open scoped InnerProductSpace

private theorem normal_dist_sq {n : ℕ} (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n)))
    (b x a : EuclideanSpace ℝ (Fin n)) (hb : b ∈ L) (ha : a ∈ L)
    (hx : x-b ∈ L.directionᗮ) :
    dist x a ^ 2 = dist x b ^ 2 + dist a b ^ 2 := by
  have hv : a-b ∈ L.direction := L.vsub_mem_direction ha hb
  have hi : inner ℝ (x-b) (a-b)=0 := Submodule.inner_left_of_mem_orthogonal hv hx
  have he : x-a=(x-b)-(a-b) := by abel
  simp only [dist_eq_norm]
  rw [he,norm_sub_sq_real,hi]
  ring

private theorem axis_characterization {n : ℕ} (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) [Nonempty L]
    (p : EuclideanSpace ℝ (Fin n)) :
    axisSphere L p =
        {x | x -ᵥ (orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) ∈ L.directionᗮ ∧
            dist x (orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) =
              dist p (orthogonalProjection L p : EuclideanSpace ℝ (Fin n))} := by
  let b : EuclideanSpace ℝ (Fin n) := orthogonalProjection L p
  have hb : b ∈ L := orthogonalProjection_mem p
  have hp : p-b ∈ L.directionᗮ := vsub_orthogonalProjection_mem_direction_orthogonal L p
  ext x
  constructor
  · intro hx
    have hL : L ≤ AffineSubspace.perpBisector x p :=
      fun a ha => AffineSubspace.mem_perpBisector_iff_dist_eq'.mpr (hx a ha)
    have hdir := AffineSubspace.direction_le hL
    have hxp : p-x ∈ L.directionᗮ := by
      rw [Submodule.mem_orthogonal]
      intro v hv
      have hv' := hdir hv
      rw [AffineSubspace.direction_perpBisector] at hv'
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp hv'
    have hxb : x-b ∈ L.directionᗮ := by
      have he : x-b=(p-b)-(p-x) := by abel
      rw [he]
      exact L.directionᗮ.sub_mem hp hxp
    exact ⟨hxb,hx b hb⟩
  · rintro ⟨hxb,hd⟩ a ha
    have h1 := normal_dist_sq L b x a hb ha hxb
    have h2 := normal_dist_sq L b p a hb ha hp
    have he : dist x b = dist p b := hd
    rw [he] at h1
    nlinarith [dist_nonneg (x := x) (y := a),dist_nonneg (x := p) (y := a)]

theorem solution {n : ℕ} (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) [Nonempty L]
    (p : EuclideanSpace ℝ (Fin n)) (hp : p ∉ L) :
    axisSphere L p =
        {x | x -ᵥ (orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) ∈ L.directionᗮ ∧
            dist x (orthogonalProjection L p : EuclideanSpace ℝ (Fin n)) =
              dist p (orthogonalProjection L p : EuclideanSpace ℝ (Fin n))} ∧
      (L : Set (EuclideanSpace ℝ (Fin n))) =
        {a | ∀ x ∈ axisSphere L p, dist x a = dist p a} := by
  refine ⟨axis_characterization L p,?_⟩
  ext a
  constructor
  · intro ha x hx
    exact hx a ha
  · intro ha
    by_contra hao
    let b : EuclideanSpace ℝ (Fin n) := orthogonalProjection L p
    let ap : EuclideanSpace ℝ (Fin n) := orthogonalProjection L a
    let v : EuclideanSpace ℝ (Fin n) := a-ap
    have hb : b ∈ L := orthogonalProjection_mem p
    have hap : ap ∈ L := orthogonalProjection_mem a
    have hv : v ∈ L.directionᗮ := vsub_orthogonalProjection_mem_direction_orthogonal L a
    have hv0 : v ≠ 0 := by
      intro hz
      have he : a=ap := sub_eq_zero.mp hz
      exact hao (he ▸ hap)
    have hr : 0 < dist p b := by
      apply dist_pos.mpr
      intro he
      exact hp (he ▸ hb)
    let t : ℝ := dist p b / ‖v‖
    have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    have ht : 0 < t := div_pos hr hnv
    have htn : t*‖v‖=dist p b := div_mul_cancel₀ _ (ne_of_gt hnv)
    let x : EuclideanSpace ℝ (Fin n) := b+t • v
    let y : EuclideanSpace ℝ (Fin n) := b-t • v
    have hxb : x-b=t • v := by dsimp [x]; abel
    have hyb : y-b=-(t • v) := by dsimp [y]; abel
    have hxd : dist x b=dist p b := by
      rw [dist_eq_norm,hxb,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
      exact htn
    have hyd : dist y b=dist p b := by
      rw [dist_eq_norm,hyb,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
      exact htn
    have hx : x ∈ axisSphere L p := by
      rw [axis_characterization L p]
      refine ⟨?_,hxd⟩
      change x-b ∈ L.directionᗮ
      rw [hxb]
      exact L.directionᗮ.smul_mem t hv
    have hy : y ∈ axisSphere L p := by
      rw [axis_characterization L p]
      refine ⟨?_,hyd⟩
      change y-b ∈ L.directionᗮ
      rw [hyb]
      exact L.directionᗮ.neg_mem (L.directionᗮ.smul_mem t hv)
    have hba : dist x a=dist y a := (ha x hx).trans (ha y hy).symm
    have hi := inner_vsub_vsub_of_dist_eq_of_dist_eq (hxd.trans hyd.symm) hba
    change inner ℝ (a-b) (y-x)=0 at hi
    have hyx : y-x=(-2*t) • v := by
      dsimp [x,y]
      module
    rw [hyx,real_inner_smul_right] at hi
    have hi0 : inner ℝ (a-b) v=0 := (mul_eq_zero.mp hi).resolve_left (by nlinarith)
    have hd : ap-b ∈ L.direction := L.vsub_mem_direction hap hb
    have ho : inner ℝ (ap-b) v=0 := Submodule.inner_right_of_mem_orthogonal hd hv
    have haeq : a-b=v+(ap-b) := by dsimp [v]; abel
    rw [haeq,inner_add_left,ho,add_zero,real_inner_self_eq_norm_sq] at hi0
    nlinarith
