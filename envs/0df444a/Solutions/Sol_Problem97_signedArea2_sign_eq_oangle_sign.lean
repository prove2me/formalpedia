-- Prove2me | solution 1 for Problem97.signedArea2_sign_eq_oangle_sign
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T06:06:29.035985+00:00
-- url     : https://prove2.me/submissions/2fad1934-3d35-4347-a6d2-724fed3097bb

/- Generated Prove2Me solution by exact Stage 2 source transformations.
   Target command: Erdos9796Proof.P97.SignedAreaOangle:2190:3913. -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Definitions.Def_Erdos9796Counting_SignedAreaOangle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

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


theorem solution
    (v vj vk : ℝ²) (hj : vj ≠ v) (hk : vk ≠ v) :
    SignType.sign (Problem97.signedArea2 v vj vk) =
      (stdOrientation.oangle (vj - v) (vk - v)).sign := by
  have hjv : vj - v ≠ 0 := sub_ne_zero.mpr hj
  have hkv : vk - v ≠ 0 := sub_ne_zero.mpr hk
  rw [signedArea2_eq_stdOrientation_areaForm]
  set o := stdOrientation with ho
  have hk' : o.kahler (vj - v) (vk - v) ≠ 0 := o.kahler_ne_zero hjv hkv
  have hnorm : 0 < ‖o.kahler (vj - v) (vk - v)‖ := norm_pos_iff.mpr hk'
  rw [Orientation.oangle, Real.Angle.sign, Real.Angle.sin_coe,
      Complex.sin_arg, o.kahler_apply_apply]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.smul_im, Complex.I_im,
             zero_add, mul_one, smul_eq_mul]
  rw [show ((o.areaForm (vj - v)) (vk - v) /
            ‖(↑(inner ℝ (vj - v) (vk - v)) : ℂ) +
              (o.areaForm (vj - v)) (vk - v) • Complex.I‖ : ℝ)
        = ‖(↑(inner ℝ (vj - v) (vk - v)) : ℂ) +
            (o.areaForm (vj - v)) (vk - v) • Complex.I‖⁻¹ *
              (o.areaForm (vj - v)) (vk - v) by ring,
      sign_mul,
      show SignType.sign
            (‖(↑(inner ℝ (vj - v) (vk - v)) : ℂ) +
              (o.areaForm (vj - v)) (vk - v) • Complex.I‖⁻¹) = 1
        from sign_pos (inv_pos.mpr hnorm), one_mul]

end Erdos9796CountingFragment_Erdos9796Proof_P97_SignedAreaOangle
