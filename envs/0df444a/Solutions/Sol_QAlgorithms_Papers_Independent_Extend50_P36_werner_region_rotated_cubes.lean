-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P36.werner_region_rotated_cubes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:42:04.543436+00:00
-- url     : https://prove2.me/submissions/bfab6a3c-0073-42ef-97ad-6328ce4e4aa4

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36
noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

end QAlgorithms.Papers.Independent.Extend50.P36

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P36
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem s110wr_osc (m u w : ℝ) :
    (∀ θ : ℝ, -1 ≤ m + Real.cos θ * u + Real.sin θ * w ∧
        m + Real.cos θ * u + Real.sin θ * w ≤ 1) ↔
      (Real.sqrt (u ^ 2 + w ^ 2) ≤ 1 - m ∧ Real.sqrt (u ^ 2 + w ^ 2) ≤ 1 + m) := by
  constructor
  · intro h
    by_cases hz : (⟨u, w⟩ : ℂ) = 0
    · have hu : u = 0 := congrArg Complex.re hz
      have hw : w = 0 := congrArg Complex.im hz
      subst hu hw
      have := h 0
      simp at this ⊢
      constructor <;> linarith
    · have hn : ‖(⟨u, w⟩ : ℂ)‖ = Real.sqrt (u ^ 2 + w ^ 2) := by
        rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
      have hpos : 0 < Real.sqrt (u ^ 2 + w ^ 2) := by rw [← hn]; exact norm_pos_iff.mpr hz
      have hsq : Real.sqrt (u ^ 2 + w ^ 2) ^ 2 = u ^ 2 + w ^ 2 :=
        Real.sq_sqrt (by positivity)
      have hc := Complex.cos_arg hz
      have hs := Complex.sin_arg (⟨u, w⟩ : ℂ)
      rw [hn] at hc hs
      simp only at hc hs
      set R := Real.sqrt (u ^ 2 + w ^ 2)
      have key : Real.cos (Complex.arg ⟨u, w⟩) * u + Real.sin (Complex.arg ⟨u, w⟩) * w = R := by
        rw [hc, hs]; field_simp; linarith
      have h1 := h (Complex.arg ⟨u, w⟩)
      have h2 := h (Complex.arg ⟨u, w⟩ + Real.pi)
      rw [Real.cos_add_pi, Real.sin_add_pi] at h2
      constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  · rintro ⟨h1, h2⟩ θ
    have hb : |Real.cos θ * u + Real.sin θ * w| ≤ Real.sqrt (u ^ 2 + w ^ 2) := by
      apply Real.abs_le_sqrt
      nlinarith [sq_nonneg (Real.cos θ * w - Real.sin θ * u), Real.sin_sq_add_cos_sq θ]
    have := abs_le.mp hb
    constructor <;> linarith [this.1, this.2]

theorem s110wr_omega : wernerCubeRoot = ⟨-1/2, Real.sqrt 3 / 2⟩ := by
  have h23 : (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  unfold wernerCubeRoot
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, h23,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  apply Complex.ext <;> norm_num

theorem s110wr_radius (a b c : ℝ) :
    (2/3 : ℝ) * ‖(c : ℂ) + wernerCubeRoot * (b : ℂ) + wernerCubeRoot ^ 2 * (a : ℂ)‖ =
      Real.sqrt ((4/9) * (a^2 + b^2 + c^2 - a*b - b*c - c*a)) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : ‖(c : ℂ) + wernerCubeRoot * (b : ℂ) + wernerCubeRoot ^ 2 * (a : ℂ)‖ ^ 2 =
      a^2 + b^2 + c^2 - a*b - b*c - c*a := by
    rw [Complex.sq_norm, Complex.normSq_apply, s110wr_omega]
    simp [sq, Complex.mul_re, Complex.mul_im]
    ring_nf
    simp only [show Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 by ring, h3]
    ring
  rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (2/3 : ℝ) * ‖(c : ℂ) + wernerCubeRoot * (b : ℂ) +
      wernerCubeRoot ^ 2 * (a : ℂ)‖), mul_pow, hn]
  norm_num

theorem solution (d : ℕ) (hd : 3 ≤ d) (x : Fin 3 → ℝ) :
    wernerRegion d (x 0) (x 1) (x 2) ↔
      ∀ theta : ℝ, ∀ i : Fin 3, -1 ≤ diagonalAxisRotation theta x i ∧ diagonalAxisRotation theta x i ≤ 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := by positivity
  set M := (x 0 + x 1 + x 2) / 3 with hM
  set R := Real.sqrt ((4/9) * (x 0^2 + x 1^2 + x 2^2 - x 0*x 1 - x 1*x 2 - x 2*x 0)) with hR
  have hreg : wernerRegion d (x 0) (x 1) (x 2) ↔ (R ≤ 1 - M ∧ R ≤ 1 + M) := by
    unfold wernerRegion
    simp only
    rw [s110wr_radius, if_neg (by omega)]
  have hR0 : R = Real.sqrt ((x 0 - M) ^ 2 + ((x 2 - x 1) / Real.sqrt 3) ^ 2) := by
    rw [hR]; congr 1; rw [div_pow, h3, hM]; ring
  have hR1 : R = Real.sqrt ((x 1 - M) ^ 2 + ((x 0 - x 2) / Real.sqrt 3) ^ 2) := by
    rw [hR]; congr 1; rw [div_pow, h3, hM]; ring
  have hR2 : R = Real.sqrt ((x 2 - M) ^ 2 + ((x 1 - x 0) / Real.sqrt 3) ^ 2) := by
    rw [hR]; congr 1; rw [div_pow, h3, hM]; ring
  have hrot : ∀ θ, diagonalAxisRotation θ x =
      ![M + Real.cos θ * (x 0 - M) + Real.sin θ * ((x 2 - x 1) / Real.sqrt 3),
        M + Real.cos θ * (x 1 - M) + Real.sin θ * ((x 0 - x 2) / Real.sqrt 3),
        M + Real.cos θ * (x 2 - M) + Real.sin θ * ((x 1 - x 0) / Real.sqrt 3)] := by
    intro θ
    unfold diagonalAxisRotation
    ext i; fin_cases i <;> simp <;> ring
  rw [hreg]
  constructor
  · intro h θ i
    rw [hrot]
    fin_cases i
    · exact (s110wr_osc _ _ _).mpr (by rw [← hR0]; exact h) θ
    · exact (s110wr_osc _ _ _).mpr (by rw [← hR1]; exact h) θ
    · exact (s110wr_osc _ _ _).mpr (by rw [← hR2]; exact h) θ
  · intro h
    rw [hR0]
    refine (s110wr_osc _ _ _).mp fun θ => ?_
    have := h θ 0
    rw [hrot] at this
    simpa using this
