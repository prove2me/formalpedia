-- Prove2me | solution 1 for SP4Mission.nonempty_homotopyEquiv_punctured_ball_sphere
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-08T05:33:26.041529+00:00
-- url     : https://prove2.me/submissions/e437f7b6-bf4e-4cb8-9b8a-49af826ce331

import Definitions.Def_SP4Sphere

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff
open SP4Mission Set unitInterval

/-!
A punctured open ball `B(c, r) ∖ {c}` in a real normed space is homotopy equivalent to the unit
sphere: radial projection `y ↦ (y - c)/‖y - c‖` onto the sphere, with homotopy inverse the
inclusion of the sphere of radius `r / 2` about `c`; the composite on the punctured ball is
homotopic to the identity through the radial homotopy `y ↦ c + ((1 - t) r/2 + t ‖y - c‖) · u(y)`,
where `u(y)` is the unit vector in the direction `y - c` (Hatcher, *Algebraic Topology*,
Chapter 0, Exercise 2, restricted to a ball).
-/

namespace PuncturedBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem sub_ne_zero_of_mem_punctured {c : E} {r : ℝ} (y : ↥(Metric.ball c r \ {c})) :
    (y : E) - c ≠ 0 :=
  sub_ne_zero.mpr fun h => y.2.2 (Set.mem_singleton_iff.mpr h)

private theorem norm_sub_pos_of_mem_punctured {c : E} {r : ℝ} (y : ↥(Metric.ball c r \ {c})) :
    0 < ‖(y : E) - c‖ :=
  norm_pos_iff.mpr (sub_ne_zero_of_mem_punctured y)

private theorem norm_sub_lt_of_mem_punctured {c : E} {r : ℝ} (y : ↥(Metric.ball c r \ {c})) :
    ‖(y : E) - c‖ < r := by
  have h := y.2.1
  rwa [Metric.mem_ball, dist_eq_norm] at h

/-- The unit vector in the direction `y - c`. -/
private noncomputable def unitDir (c : E) (y : E) : E := ‖y - c‖⁻¹ • (y - c)

private theorem norm_unitDir {c : E} {r : ℝ} (y : ↥(Metric.ball c r \ {c})) :
    ‖unitDir c (y : E)‖ = 1 := by
  unfold unitDir
  rw [norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero_of_mem_punctured y))]

private theorem continuous_unitDir_punctured (c : E) (r : ℝ) :
    Continuous fun y : ↥(Metric.ball c r \ {c}) => unitDir c (y : E) := by
  unfold unitDir
  have hsub : Continuous fun y : ↥(Metric.ball c r \ {c}) => (y : E) - c :=
    continuous_subtype_val.sub continuous_const
  exact (hsub.norm.inv₀ fun y => norm_ne_zero_iff.mpr (sub_ne_zero_of_mem_punctured y)).smul hsub

/-- A point `c + s • u` with `u` a unit vector and `0 < s < r` lies in the punctured ball. -/
private theorem mem_punctured_of_unit {c : E} {r : ℝ} {u : E} (hu : ‖u‖ = 1) {s : ℝ} (hs : 0 < s)
    (hsr : s < r) : c + s • u ∈ Metric.ball c r \ {c} := by
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu, mul_one,
      Real.norm_eq_abs, abs_of_pos hs]
    exact hsr
  · intro h
    rw [Set.mem_singleton_iff] at h
    have h0 : s • u = 0 := by simpa using h
    rw [smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact hs.ne' h0
    · rw [h0, norm_zero] at hu
      exact zero_ne_one hu

/-- Radial projection of the punctured ball onto the unit sphere. -/
private noncomputable def toSphere (c : E) (r : ℝ) :
    C(↥(Metric.ball c r \ {c}), ↥(Metric.sphere (0 : E) 1)) where
  toFun y := ⟨unitDir c (y : E), mem_sphere_zero_iff_norm.mpr (norm_unitDir y)⟩
  continuous_toFun := (continuous_unitDir_punctured c r).subtype_mk _

/-- Inclusion of the sphere of radius `r / 2` about `c` into the punctured ball. -/
private noncomputable def ofSphere (c : E) {r : ℝ} (hr : 0 < r) :
    C(↥(Metric.sphere (0 : E) 1), ↥(Metric.ball c r \ {c})) where
  toFun u := ⟨c + (r / 2) • (u : E),
    mem_punctured_of_unit (mem_sphere_zero_iff_norm.mp u.2) (by linarith) (by linarith)⟩
  continuous_toFun := (continuous_const.add (continuous_const.smul continuous_subtype_val)).subtype_mk _

private theorem toSphere_ofSphere (c : E) {r : ℝ} (hr : 0 < r) (u : ↥(Metric.sphere (0 : E) 1)) :
    toSphere c r (ofSphere c hr u) = u := by
  apply Subtype.ext
  have hu : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  show unitDir c (c + (r / 2) • (u : E)) = u
  unfold unitDir
  rw [add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith),
    smul_smul, inv_mul_cancel₀ (by linarith), one_smul]

/-- The radial scale at time `t`: interpolates from `r / 2` (at `t = 0`) to `‖y - c‖` (at `t = 1`). -/
private noncomputable def radialScale (c : E) (r : ℝ) (t : ℝ) (y : E) : ℝ :=
  (1 - t) * (r / 2) + t * ‖y - c‖

private theorem radialScale_pos {c : E} {r : ℝ} (hr : 0 < r) (t : I) (y : ↥(Metric.ball c r \ {c})) :
    0 < radialScale c r t (y : E) := by
  unfold radialScale
  have h1 := norm_sub_pos_of_mem_punctured y
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rcases eq_or_lt_of_le ht1 with h | h
  · rw [h]
    simpa using sub_ne_zero_of_mem_punctured y
  · have h2 : 0 < (1 - (t : ℝ)) * (r / 2) := by nlinarith
    have h3 : 0 ≤ (t : ℝ) * ‖(y : E) - c‖ := mul_nonneg ht0 h1.le
    linarith

private theorem radialScale_lt {c : E} {r : ℝ} (hr : 0 < r) (t : I) (y : ↥(Metric.ball c r \ {c})) :
    radialScale c r t (y : E) < r := by
  unfold radialScale
  have h1 := norm_sub_lt_of_mem_punctured y
  have ht0 : (0 : ℝ) ≤ t := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  rcases eq_or_lt_of_le ht1 with h | h
  · rw [h]
    simpa using h1
  · have h2 : (1 - (t : ℝ)) * (r / 2) < (1 - (t : ℝ)) * r :=
      mul_lt_mul_of_pos_left (by linarith) (by linarith)
    have h3 : (t : ℝ) * ‖(y : E) - c‖ ≤ (t : ℝ) * r := mul_le_mul_of_nonneg_left h1.le ht0
    linarith

private theorem continuous_radialScale (c : E) (r : ℝ) :
    Continuous fun p : I × ↥(Metric.ball c r \ {c}) => radialScale c r (p.1 : ℝ) (p.2 : E) := by
  unfold radialScale
  fun_prop

/-- The radial deformation of the punctured ball onto the sphere of radius `r / 2`:
a homotopy from `ofSphere ∘ toSphere` to the identity. -/
private noncomputable def radialHomotopy (c : E) {r : ℝ} (hr : 0 < r) :
    ContinuousMap.Homotopy ((ofSphere c hr).comp (toSphere c r))
      (ContinuousMap.id ↥(Metric.ball c r \ {c})) where
  toFun p := ⟨c + radialScale c r (p.1 : ℝ) (p.2 : E) • unitDir c (p.2 : E),
    mem_punctured_of_unit (norm_unitDir p.2) (radialScale_pos hr p.1 p.2) (radialScale_lt hr p.1 p.2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.add ((continuous_radialScale c r).smul
      ((continuous_unitDir_punctured c r).comp continuous_snd))
  map_zero_left y := by
    apply Subtype.ext
    show c + radialScale c r ((0 : I) : ℝ) (y : E) • unitDir c (y : E) = c + (r / 2) • unitDir c (y : E)
    simp [radialScale]
  map_one_left y := by
    apply Subtype.ext
    show c + radialScale c r ((1 : I) : ℝ) (y : E) • unitDir c (y : E) = (y : E)
    simp only [radialScale, Set.Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
    unfold unitDir
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero_of_mem_punctured y)),
      one_smul, add_sub_cancel]

/-- A punctured open ball is homotopy equivalent to the unit sphere. -/
private noncomputable def puncturedBallHomotopyEquivSphere (c : E) {r : ℝ} (hr : 0 < r) :
    ContinuousMap.HomotopyEquiv ↥(Metric.ball c r \ {c}) ↥(Metric.sphere (0 : E) 1) where
  toFun := toSphere c r
  invFun := ofSphere c hr
  left_inv := ⟨radialHomotopy c hr⟩
  right_inv := by
    have h : (toSphere c r).comp (ofSphere c hr) = ContinuousMap.id _ := by
      ext u
      exact congrArg Subtype.val (toSphere_ofSphere c hr u)
    rw [h]


end PuncturedBall

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) {r : ℝ} (hr : 0 < r) :
    Nonempty (ContinuousMap.HomotopyEquiv ↥(Metric.ball c r \ {c}) ↥(Metric.sphere (0 : E) 1)) :=
  ⟨PuncturedBall.puncturedBallHomotopyEquivSphere c hr⟩
