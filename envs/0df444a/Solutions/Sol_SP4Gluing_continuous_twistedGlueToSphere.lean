-- Prove2me | solution 1 for SP4Gluing.continuous_twistedGlueToSphere
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T01:54:57.879141+00:00
-- url     : https://prove2.me/submissions/82721419-7342-47bb-ae4d-af0c48eecb5b

import Mathlib
import Definitions.Def_SP4Gluing

set_option autoImplicit false
open Set Metric SP4Gluing SPC4Disk

namespace ContAux

variable {m : ℕ}

/-- `alexanderExt` preserves the radius exactly: this is the identity that makes the
radial factor cancel the discontinuity of the direction map at the centre. -/
lemma alexanderExt_norm
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ‖(alexanderExt φ w).val‖ = ‖w.val‖ := by
  show ‖‖w.val‖ • (φ (unitOr diskNorth w.val)).val‖ = ‖w.val‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    mem_sphere_zero_iff_norm.mp (φ (unitOr diskNorth w.val)).2, mul_one]

/-- The punctured disk, an open subset of the closed disk. -/
lemma isOpen_punctured :
    IsOpen { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | w.val ≠ 0 } :=
  isOpen_ne.preimage continuous_subtype_val

/-- Away from the centre, `alexanderExt φ` is a composite of continuous maps:
the radial unit map is continuous there, `φ` is a homeomorphism, and the scalar
`‖w‖` is continuous. -/
lemma continuousOn_alexanderExt
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ContinuousOn (alexanderExt φ)
      { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | w.val ≠ 0 } := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hval : Continuous
      (fun z : { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | w.val ≠ 0 } =>
        z.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hunit : Continuous
      (fun z : { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | w.val ≠ 0 } =>
        unitOr diskNorth z.val.val) :=
    (continuousOn_unitOr diskNorth).comp_continuous hval fun z => z.2
  have himg : Continuous
      (fun z : { w : closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | w.val ≠ 0 } =>
        (φ (unitOr diskNorth z.val.val)).val) :=
    continuous_subtype_val.comp (φ.continuous.comp hunit)
  exact Continuous.subtype_mk (hval.norm.smul himg) _

/-- The Alexander extension is continuous. Off the centre this is the composite
above; at the centre it is forced by `‖alexanderExt φ w‖ = ‖w‖`, which makes the
map distance-preserving *relative to the centre*. -/
theorem continuous_alexanderExt
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Continuous (alexanderExt φ) := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases h : w.val = 0
  · -- the centre: squeeze by the exact radius identity
    have h0 : (alexanderExt φ w).val = 0 := by
      show ‖w.val‖ • (φ (unitOr diskNorth w.val)).val = 0
      rw [h, norm_zero, zero_smul]
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro w' hw'
    have e1 : dist (alexanderExt φ w') (alexanderExt φ w) = ‖(alexanderExt φ w').val‖ := by
      rw [Subtype.dist_eq, h0, dist_zero_right]
    have e2 : dist w' w = ‖w'.val‖ := by
      rw [Subtype.dist_eq, h, dist_zero_right]
    rw [e1, alexanderExt_norm, ← e2]
    exact hw'
  · exact (continuousOn_alexanderExt φ).continuousAt (isOpen_punctured.mem_nhds h)

end ContAux

open ContAux

theorem solution {m : ℕ}
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    Continuous (twistedGlueToSphere φ) := by
  refine continuous_quot_lift _ ?_
  apply Continuous.sumElim
  · exact continuous_subtype_val.comp upperHemisphereHomeoDisk.symm.continuous
  · exact continuous_subtype_val.comp
      (lowerHemisphereHomeoDiskRefl.symm.continuous.comp (continuous_alexanderExt φ.symm))
