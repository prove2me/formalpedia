-- Prove2me | solution 1 for Plasticity.BallMap.norm_map_sub_map_eq_of_map_smul
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T02:24:25.37346+00:00
-- url     : https://prove2.me/submissions/efb825d0-21e4-44e0-ba3b-fcd3dd0461e1

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Module

/-!
# Isometry between homogeneous points

Zavarzina, arXiv:1704.06961, Lemmas 2.4–2.5; the repository's version is
`expositions/faces/finite_faces_boundary_crossing.md` §6, Step 2.
If `F` is nonexpansive on the closed unit ball of `X`, maps the unit sphere of `X` into that of
`Y`, and is odd-homogeneous on the segments `[-x, x]` and `[-y, y]`, then
`‖F x - F y‖ = ‖x - y‖`.

The one-sided derivative calculus of the exposition is replaced by one triangle inequality at a
unit vector `u` (`two_le`) and the derivative of `s ↦ ‖(x - y) + s • y‖` at a point of
differentiability near `0` (Rademacher's theorem on the line).
-/

open Filter Topology Set MeasureTheory

namespace Sol_Plasticity_BallMap_norm_map_sub_map_eq_of_map_smul

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The pointwise inequality at a unit vector `u`: from
`2 • F u = (F u + a • F y) + (F u - a • F x) + a • (F x - F y)`. -/
theorem two_le {F : X → Y}
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    {x y : X} (hx : x ∈ Metric.closedBall (0 : X) 1) (hy : y ∈ Metric.closedBall (0 : X) 1)
    (hFx : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • x) = t • F x)
    (hFy : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • y) = t • F y)
    {u : X} (hu : ‖u‖ = 1) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    2 ≤ ‖u + a • y‖ + ‖u - a • x‖ + a * ‖F x - F y‖ := by
  have huB : u ∈ Metric.closedBall (0 : X) 1 := by simp [hu]
  have huS : u ∈ Metric.sphere (0 : X) 1 := by simp [hu]
  have hFu : ‖F u‖ = 1 := by simpa using hsphere huS
  have hxn : ‖x‖ ≤ 1 := by simpa using hx
  have hyn : ‖y‖ ≤ 1 := by simpa using hy
  have hay : (-a) • y ∈ Metric.closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ha0]
    nlinarith [norm_nonneg y]
  have hax : a • x ∈ Metric.closedBall (0 : X) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
    nlinarith [norm_nonneg x]
  have h1 : ‖F u + a • F y‖ ≤ ‖u + a • y‖ := by
    have := hlip.dist_le_mul u huB ((-a) • y) hay
    rw [hFy (-a) ⟨by linarith, by linarith⟩] at this
    simpa [dist_eq_norm, sub_neg_eq_add, neg_smul] using this
  have h2 : ‖F u - a • F x‖ ≤ ‖u - a • x‖ := by
    have := hlip.dist_le_mul u huB (a • x) hax
    rw [hFx a ⟨by linarith, ha1⟩] at this
    simpa [dist_eq_norm] using this
  have h3 : (2 : ℝ) ≤ ‖F u + a • F y‖ + ‖F u - a • F x‖ + a * ‖F x - F y‖ := by
    have e : (2 : ℝ) • F u = (F u + a • F y) + (F u - a • F x) + a • (F x - F y) := by module
    have h2u : ‖(2 : ℝ) • F u‖ = 2 := by rw [norm_smul, hFu]; norm_num
    calc (2 : ℝ) = ‖(2 : ℝ) • F u‖ := h2u.symm
      _ = ‖(F u + a • F y) + (F u - a • F x) + a • (F x - F y)‖ := by rw [e]
      _ ≤ ‖F u + a • F y‖ + ‖F u - a • F x‖ + ‖a • (F x - F y)‖ := norm_add₃_le
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha0]
  linarith

/-- `two_le` rescaled to a nonzero vector `p` in place of the unit vector `‖p‖⁻¹ • p`. -/
theorem two_mul_le {F : X → Y}
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    {x y : X} (hx : x ∈ Metric.closedBall (0 : X) 1) (hy : y ∈ Metric.closedBall (0 : X) 1)
    (hFx : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • x) = t • F x)
    (hFy : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • y) = t • F y)
    {p : X} (hp : p ≠ 0) {c : ℝ} (hc0 : 0 < c) (hcp : c ≤ ‖p‖) :
    2 * ‖p‖ ≤ ‖p + c • y‖ + ‖p - c • x‖ + c * ‖F x - F y‖ := by
  have hr0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hu : ‖‖p‖⁻¹ • p‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ hr0.ne'
  have ha0 : 0 < c / ‖p‖ := div_pos hc0 hr0
  have ha1 : c / ‖p‖ ≤ 1 := (div_le_one hr0).2 hcp
  have h := two_le hlip hsphere hx hy hFx hFy hu ha0 ha1
  have hrc : ‖p‖ * (c / ‖p‖) = c := by field_simp
  have e1 : p + c • y = ‖p‖ • (‖p‖⁻¹ • p + (c / ‖p‖) • y) := by
    rw [smul_add, smul_smul, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, hrc]
  have e2 : p - c • x = ‖p‖ • (‖p‖⁻¹ • p - (c / ‖p‖) • x) := by
    rw [smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul, hrc]
  rw [e1, e2, norm_smul, norm_smul, norm_norm]
  calc 2 * ‖p‖ = ‖p‖ * 2 := mul_comm _ _
    _ ≤ ‖p‖ * (‖‖p‖⁻¹ • p + (c / ‖p‖) • y‖ + ‖‖p‖⁻¹ • p - (c / ‖p‖) • x‖
          + c / ‖p‖ * ‖F x - F y‖) := mul_le_mul_of_nonneg_left h hr0.le
    _ = _ := by rw [mul_add, mul_add, ← mul_assoc, hrc]

/-- The inequality along the line `s ↦ (x - y) + s • y`. -/
theorem line_le {F : X → Y}
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    {x y : X} (hx : x ∈ Metric.closedBall (0 : X) 1) (hy : y ∈ Metric.closedBall (0 : X) 1)
    (hFx : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • x) = t • F x)
    (hFy : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • y) = t • F y)
    {s₀ c : ℝ} (hs₀ : |s₀| ≤ 1) (hpos : 0 < ‖(x - y) + s₀ • y‖) (hc0 : 0 < c)
    (hcf : c ≤ ‖(x - y) + s₀ • y‖) (hc1 : c ≤ 1) :
    2 * ‖(x - y) + s₀ • y‖ ≤ ‖(x - y) + (s₀ + c) • y‖
      + (1 - c) * ‖(x - y) + (s₀ - c * (1 - s₀)) • y‖ + 2 * c ^ 2 + c * ‖F x - F y‖ := by
  have hp : (x - y) + s₀ • y ≠ 0 := norm_pos_iff.1 hpos
  have h := two_mul_le hlip hsphere hx hy hFx hFy hp hc0 hcf
  have e1 : (x - y) + s₀ • y + c • y = (x - y) + (s₀ + c) • y := by module
  have e2 : (x - y) + s₀ • y - c • x
      = (1 - c) • ((x - y) + (s₀ - c * (1 - s₀)) • y) - (c ^ 2 * (1 - s₀)) • y := by module
  rw [e1, e2] at h
  have hyn : ‖y‖ ≤ 1 := by simpa using hy
  have hs := abs_le.1 hs₀
  have h1s : 0 ≤ 1 - s₀ := by linarith
  have hc2 : 0 ≤ c ^ 2 * (1 - s₀) := mul_nonneg (sq_nonneg c) h1s
  have h3 : ‖(1 - c) • ((x - y) + (s₀ - c * (1 - s₀)) • y) - (c ^ 2 * (1 - s₀)) • y‖
      ≤ (1 - c) * ‖(x - y) + (s₀ - c * (1 - s₀)) • y‖ + 2 * c ^ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - c), abs_of_nonneg hc2]
    have : c ^ 2 * (1 - s₀) * ‖y‖ ≤ 2 * c ^ 2 := by
      calc c ^ 2 * (1 - s₀) * ‖y‖ ≤ c ^ 2 * (1 - s₀) * 1 := mul_le_mul_of_nonneg_left hyn hc2
        _ ≤ 2 * c ^ 2 := by nlinarith [sq_nonneg c]
    linarith
  linarith

/-- The derivative step: if the inequality of `line_le` holds for all small `c > 0` and `f` has
derivative `L` at `s₀`, then `f s₀ - L * s₀ ≤ K` (the right-hand side has derivative
`L * s₀ - f s₀` at `c = 0` and value `2 * f s₀` there). -/
theorem deriv_bound (f : ℝ → ℝ) (K L s₀ : ℝ) (hf : HasDerivAt f L s₀) (hpos : 0 < f s₀)
    (h : ∀ c, 0 < c → c ≤ f s₀ → c ≤ 1 →
      2 * f s₀ ≤ f (s₀ + c) + (1 - c) * f (s₀ - c * (1 - s₀)) + 2 * c ^ 2 + c * K) :
    f s₀ - L * s₀ ≤ K := by
  set g : ℝ → ℝ := fun c => f (s₀ + c) + (1 - c) * f (s₀ - c * (1 - s₀)) + 2 * c ^ 2 with hg
  have hA : HasDerivAt (fun c => f (s₀ + c)) L 0 := by
    apply HasDerivAt.comp_const_add; simpa using hf
  have hB : HasDerivAt (fun c : ℝ => s₀ - c * (1 - s₀)) (-(1 * (1 - s₀))) 0 :=
    ((hasDerivAt_id (0 : ℝ)).mul_const (1 - s₀)).const_sub s₀
  have hf' : HasDerivAt f L (s₀ - 0 * (1 - s₀)) := by simpa using hf
  have hC : HasDerivAt (fun c => f (s₀ - c * (1 - s₀))) (L * (-(1 * (1 - s₀)))) 0 :=
    hf'.comp (0 : ℝ) hB
  have hD : HasDerivAt (fun c : ℝ => 1 - c) (-1) 0 := (hasDerivAt_id (0 : ℝ)).const_sub 1
  have hE := hD.mul hC
  have hP := (hasDerivAt_pow 2 (0 : ℝ)).const_mul 2
  have hG : HasDerivAt g (L * s₀ - f s₀) 0 :=
    ((hA.add hE).add hP).congr_deriv (by norm_num; ring)
  have hlim := hG.tendsto_slope_zero_right
  have hg0 : g 0 = 2 * f s₀ := by simp [hg]; ring
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), -K ≤ t⁻¹ • (g (0 + t) - g 0) := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hpos one_pos)] with t ht
    have ht0 : 0 < t := ht.1
    have h1 := h t ht0 (le_of_lt (lt_of_lt_of_le ht.2 (min_le_left _ _)))
      (le_of_lt (lt_of_lt_of_le ht.2 (min_le_right _ _)))
    rw [smul_eq_mul, le_inv_mul_iff₀ ht0, zero_add, hg0]
    show t * -K ≤ f (s₀ + t) + (1 - t) * f (s₀ - t * (1 - s₀)) + 2 * t ^ 2 - 2 * f s₀
    linarith
  have := ge_of_tendsto hlim hev
  linarith

/-- The reverse inequality: `‖x - y‖ ≤ ‖F x - F y‖`. -/
theorem main {F : X → Y}
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    {x y : X} (hx : x ∈ Metric.closedBall (0 : X) 1) (hy : y ∈ Metric.closedBall (0 : X) 1)
    (hFx : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • x) = t • F x)
    (hFy : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • y) = t • F y) :
    ‖x - y‖ ≤ ‖F x - F y‖ := by
  set K := ‖F x - F y‖ with hK
  by_contra hlt
  push Not at hlt
  have hK0 : 0 ≤ K := norm_nonneg _
  set f : ℝ → ℝ := fun s => ‖(x - y) + s • y‖ with hf
  have hyn : ‖y‖ ≤ 1 := by simpa using hy
  have hflip : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    calc |f s - f t| ≤ ‖((x - y) + s • y) - ((x - y) + t • y)‖ := abs_norm_sub_norm_le _ _
      _ = |s - t| * ‖y‖ := by
          rw [show ((x - y) + s • y) - ((x - y) + t • y) = (s - t) • y by module, norm_smul,
            Real.norm_eq_abs]
      _ ≤ |s - t| := mul_le_of_le_one_right (abs_nonneg _) hyn
  set ε := (‖x - y‖ - K) / 4 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set δ := min ε (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min hε0 (by norm_num)
  obtain ⟨s₀, hs₀, hdiff⟩ : ∃ s ∈ Ioo (-δ) δ, DifferentiableAt ℝ f s := by
    by_contra hcon
    push Not at hcon
    have hsub : Ioo (-δ) δ ⊆ {s | ¬ DifferentiableAt ℝ f s} := fun s hs => hcon s hs
    have h0 : volume {s | ¬ DifferentiableAt ℝ f s} = 0 := ae_iff.1 hflip.ae_differentiableAt_real
    have h1 := measure_mono_null hsub h0
    rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h1
    linarith
  have habs : |s₀| < δ := abs_lt.2 ⟨hs₀.1, hs₀.2⟩
  have habsε : |s₀| < ε := lt_of_lt_of_le habs (min_le_left _ _)
  have habs1 : |s₀| ≤ 1 := by
    have : δ ≤ 1 / 2 := min_le_right _ _
    linarith
  have hLb : |deriv f s₀| ≤ 1 := by
    simpa using norm_deriv_le_of_lipschitz (x₀ := s₀) hflip
  have hfs : ‖x - y‖ - |s₀| ≤ f s₀ := by
    have h1 := hflip.dist_le_mul s₀ 0
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, sub_zero] at h1
    have h2 : f 0 = ‖x - y‖ := by simp [hf]
    rw [h2] at h1
    linarith [(abs_le.1 h1).1]
  have hpos : 0 < f s₀ := by linarith
  have key := deriv_bound f K (deriv f s₀) s₀ hdiff.hasDerivAt hpos
    (fun c hc0 hcf hc1 => line_le hlip hsphere hx hy hFx hFy habs1 hpos hc0 hcf hc1)
  have hLs : deriv f s₀ * s₀ ≤ |s₀| := by
    calc deriv f s₀ * s₀ ≤ |deriv f s₀ * s₀| := le_abs_self _
      _ = |deriv f s₀| * |s₀| := abs_mul _ _
      _ ≤ 1 * |s₀| := mul_le_mul_of_nonneg_right hLb (abs_nonneg _)
      _ = |s₀| := one_mul _
  linarith

theorem of_mem_ball {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (x y : X) (hx : x ∈ Metric.closedBall (0 : X) 1) (hy : y ∈ Metric.closedBall (0 : X) 1)
    (hFx : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • x) = t • F x)
    (hFy : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • y) = t • F y) :
    ‖F x - F y‖ = ‖x - y‖ := by
  refine le_antisymm ?_
    (Sol_Plasticity_BallMap_norm_map_sub_map_eq_of_map_smul.main hlip hsphere hx hy hFx hFy)
  simpa [dist_eq_norm] using hlip.dist_le_mul x hx y hy

end Sol_Plasticity_BallMap_norm_map_sub_map_eq_of_map_smul

theorem solution {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : X → Y)
    (hlip : LipschitzOnWith 1 F (Metric.closedBall (0 : X) 1))
    (hsphere : Set.MapsTo F (Metric.sphere (0 : X) 1) (Metric.sphere (0 : Y) 1))
    (x y : X)
    (hFx : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • x) = t • F x)
    (hFy : ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • y) = t • F y) :
    ‖F x - F y‖ = ‖x - y‖ := by
  -- rescale both points into the ball; homogeneity carries the identity back
  set r : ℝ := max 1 (max ‖x‖ ‖y‖) with hr
  have hr1 : 1 ≤ r := le_max_left _ _
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hri : r⁻¹ ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [inv_pos.mpr hr0], inv_le_one_of_one_le₀ hr1⟩
  have hball : ∀ z : X, ‖z‖ ≤ r → r⁻¹ • z ∈ Metric.closedBall (0 : X) 1 := by
    intro z hz
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hr0).le]
    calc r⁻¹ * ‖z‖ ≤ r⁻¹ * r := by gcongr
      _ = 1 := inv_mul_cancel₀ hr0.ne'
  have hscale : ∀ z : X, (∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • z) = t • F z) →
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, F (t • r⁻¹ • z) = t • F (r⁻¹ • z) := by
    intro z hz t ht
    have htr : t * r⁻¹ ∈ Set.Icc (-1 : ℝ) 1 := by
      have h1 : |t * r⁻¹| ≤ 1 := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hr0)]
        calc |t| * r⁻¹ ≤ 1 * 1 := by
              gcongr
              · exact abs_le.mpr ⟨ht.1, ht.2⟩
              · exact inv_le_one_of_one_le₀ hr1
          _ = 1 := one_mul 1
      exact ⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩
    rw [smul_smul, hz _ htr, hz _ hri, smul_smul]
  have key := Sol_Plasticity_BallMap_norm_map_sub_map_eq_of_map_smul.of_mem_ball F hlip hsphere
    (r⁻¹ • x) (r⁻¹ • y) (hball x (le_trans (le_max_left _ _) (le_max_right _ _)))
    (hball y (le_trans (le_max_right _ _) (le_max_right _ _))) (hscale x hFx) (hscale y hFy)
  rw [hFx _ hri, hFy _ hri, ← smul_sub, ← smul_sub, norm_smul, norm_smul] at key
  exact mul_left_cancel₀ (norm_ne_zero_iff.mpr (inv_ne_zero hr0.ne')) key
