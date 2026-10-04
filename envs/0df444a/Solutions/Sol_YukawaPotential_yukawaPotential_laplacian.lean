-- Prove2me | solution 1 for YukawaPotential.yukawaPotential_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T02:58:16.476328+00:00
-- url     : https://prove2.me/submissions/b0eb9b5c-c491-4cfe-a276-d5b3f89e8dab

import Mathlib
import Definitions.Def_YukawaPotential_Defs

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace YukawaLapAux

theorem hasFDerivAt_norm_ne (y : EuclideanSpace ℝ (Fin 3)) (hy : y ≠ 0) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) => ‖z‖) (‖y‖⁻¹ • innerSL ℝ y) y := by
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have h1 := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have h2 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖y‖ ^ 2))) (‖y‖ ^ 2) :=
    Real.hasDerivAt_sqrt (by positivity)
  have h3 := h2.comp_hasFDerivAt y h1
  have heq : (fun z : EuclideanSpace ℝ (Fin 3) => ‖z‖) =
      Real.sqrt ∘ (fun z : EuclideanSpace ℝ (Fin 3) => ‖z‖ ^ 2) := by
    ext z; simp [Real.sqrt_sq (norm_nonneg z)]
  have h4 : (1 / (2 * Real.sqrt (‖y‖ ^ 2))) • (2 • innerSL ℝ y) = ‖y‖⁻¹ • innerSL ℝ y := by
    rw [Real.sqrt_sq hpos.le]
    ext v
    simp
    field_simp
  rw [heq]
  rw [h4] at h3
  exact h3

theorem hasDerivAt_e (μ r : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(μ * s))) (Real.exp (-(μ * r)) * (-μ)) r := by
  have h0 : HasDerivAt (fun s : ℝ => -(μ * s)) (-(μ * 1)) r :=
    ((hasDerivAt_id' r).const_mul μ).neg
  exact h0.exp.congr_deriv (by ring)

theorem hasDerivAt_h (K μ r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => K * Real.exp (-(μ * s)) / s)
      ((-K * Real.exp (-(μ * r)) * (μ * r + 1) / r ^ 3) * r) r := by
  have := ((hasDerivAt_e μ r).const_mul K).div (hasDerivAt_id' r) hr
  exact this.congr_deriv (by field_simp; ring)

theorem hasDerivAt_c (K μ r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => -K * Real.exp (-(μ * s)) * (μ * s + 1) / s ^ 3)
      (K * Real.exp (-(μ * r)) * (μ ^ 2 / r ^ 2 + 3 * (μ * r + 1) / r ^ 4)) r := by
  have hl : HasDerivAt (fun s : ℝ => μ * s + 1) (μ * 1) r :=
    ((hasDerivAt_id' r).const_mul μ).add_const 1
  have hp : HasDerivAt (fun s : ℝ => s ^ 3) (↑3 * r ^ (3 - 1)) r := hasDerivAt_pow 3 r
  have := (((hasDerivAt_e μ r).const_mul (-K)).mul hl).div hp (pow_ne_zero 3 hr)
  exact this.congr_deriv (by simp only [Pi.mul_apply]; field_simp; ring)

theorem contDiffAt_f (K μ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => K * Real.exp (-(μ * ‖y‖)) / ‖y‖) x := by
  have hn : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖) x := contDiffAt_norm ℝ hx
  have he : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => Real.exp (-(μ * ‖y‖))) x :=
    Real.contDiff_exp.contDiffAt.comp x ((contDiffAt_const.mul hn).neg)
  exact (contDiffAt_const.mul he).div hn (norm_ne_zero_iff.mpr hx)

theorem second (K μ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0)
    (v : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => K * Real.exp (-(μ * ‖y‖)) / ‖y‖)) x v v
      = (-K * Real.exp (-(μ * ‖x‖)) * (μ * ‖x‖ + 1) / ‖x‖ ^ 3) * inner ℝ v v +
        (K * Real.exp (-(μ * ‖x‖)) * (μ ^ 2 / ‖x‖ ^ 2 + 3 * (μ * ‖x‖ + 1) / ‖x‖ ^ 4)) *
          ‖x‖⁻¹ * inner ℝ x v ^ 2 := by
  set c : ℝ → ℝ := fun s => -K * Real.exp (-(μ * s)) * (μ * s + 1) / s ^ 3 with hc
  set f : EuclideanSpace ℝ (Fin 3) → ℝ := fun y => K * Real.exp (-(μ * ‖y‖)) / ‖y‖ with hf
  have hf1 : ∀ y : EuclideanSpace ℝ (Fin 3), y ≠ 0 →
      HasFDerivAt f (c ‖y‖ • innerSL ℝ y) y := by
    intro y hy
    have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    have := (hasDerivAt_h K μ ‖y‖ hn).comp_hasFDerivAt y (hasFDerivAt_norm_ne y hy)
    have e : (-K * Real.exp (-(μ * ‖y‖)) * (μ * ‖y‖ + 1) / ‖y‖ ^ 3 * ‖y‖) • ‖y‖⁻¹ • innerSL ℝ y
        = c ‖y‖ • innerSL ℝ y := by
      rw [smul_smul]
      congr 1
      simp only [hc]
      field_simp
    rw [e] at this
    exact this
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((contDiffAt_f K μ x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hstep : fderiv ℝ (fderiv ℝ f) x v v = fderiv ℝ (fun y => fderiv ℝ f y v) x v := by
    rw [fderiv_clm_apply hdiff (differentiableAt_const v)]
    simp
  have hev : (fun y => fderiv ℝ f y v) =ᶠ[𝓝 x] fun y => c ‖y‖ * innerSL ℝ v y := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [(hf1 y hy).fderiv]
    simp [real_inner_comm]
  have hcn := (hasDerivAt_c K μ ‖x‖ (norm_ne_zero_iff.mpr hx)).comp_hasFDerivAt x
      (hasFDerivAt_norm_ne x hx)
  have hG : HasFDerivAt (fun y => c ‖y‖ * innerSL ℝ v y) _ x := hcn.mul (innerSL ℝ v).hasFDerivAt
  rw [hstep, hev.fderiv_eq, hG.fderiv]
  simp [real_inner_comm]
  ring

theorem lap_radial (K μ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    Laplacian.laplacian
        (fun y : EuclideanSpace ℝ (Fin 3) => K * Real.exp (-(μ * ‖y‖)) / ‖y‖) x =
      μ ^ 2 * (K * Real.exp (-(μ * ‖x‖)) / ‖x‖) := by
  set b := EuclideanSpace.basisFun (Fin 3) ℝ with hbdef
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [second K μ x hx]
  have hb : ∀ i, inner ℝ (b i) (b i) = (1 : ℝ) := fun i => by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]; norm_num
  have hsum : ∑ i, inner ℝ x (b i) ^ 2 = ‖x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner x x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sq, real_inner_comm (b i) x]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [hb, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp
  ring

end YukawaLapAux

open YukawaPotential in
theorem solution (g α m : ℝ) (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin 3) => yukawaPotential g α m ‖y‖) x =
      (α * m) ^ 2 * yukawaPotential g α m ‖x‖ := by
  have := YukawaLapAux.lap_radial (-g ^ 2) (α * m) x hx
  simp only [yukawaPotential]
  exact this

