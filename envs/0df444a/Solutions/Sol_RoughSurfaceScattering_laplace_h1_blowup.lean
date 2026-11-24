-- Prove2me | solution 1 for RoughSurfaceScattering.laplace_h1_blowup
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:37:15.913077+00:00
-- url     : https://prove2.me/submissions/d422b3c9-ba01-4618-a48a-e098c7545ffe

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic
import Theorems.Thm_RoughSurfaceScattering_dipole_l2_blowup

open MeasureTheory Metric
open RoughSurfaceScattering

lemma phi0_contDiffOn (z : R2) :
    ContDiffOn ℝ 1 (fun x' : R2 => Phi 0 x' z) {x | x ≠ z} := by
  intro x hx
  have hx' : x - z ≠ 0 := sub_ne_zero.mpr hx
  have hn : ContDiffAt ℝ 1 (fun x' : R2 => ‖x' - z‖) x :=
    (contDiffAt_norm ℝ hx').comp x ((contDiffAt_id).sub contDiffAt_const)
  have hpos : 0 < ‖x - z‖ := norm_pos_iff.mpr hx'
  have hinv : ContDiffAt ℝ 1 (fun x' : R2 => 1 / ‖x' - z‖) x := by
    have := (contDiffAt_inv ℝ hpos.ne').comp x hn
    simpa [one_div, Function.comp_def] using this
  have hlog : ContDiffAt ℝ 1 (fun x' : R2 => Real.log (1 / ‖x' - z‖)) x :=
    (Real.contDiffAt_log.mpr (by positivity)).comp x hinv
  have hreal : ContDiffAt ℝ 1
      (fun x' : R2 => 1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖)) x :=
    contDiffAt_const.mul hlog
  have hc : ContDiffAt ℝ 1
      (fun x' : R2 => ((1 / (2 * Real.pi) * Real.log (1 / ‖x' - z‖) : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hreal
  simpa [Phi] using hc.contDiffWithinAt

lemma phi0_differentiableAt (z x : R2) (hx : x ≠ z) :
    DifferentiableAt ℝ (fun x' : R2 => Phi 0 x' z) x :=
  ((phi0_contDiffOn z).contDiffAt (isOpen_ne.mem_nhds hx)).differentiableAt one_ne_zero

/-- `|L ν|² ≤ |L e₁|² + |L e₂|²` for a unit vector `ν`. -/
lemma clm_unit_sq_le (L : R2 →L[ℝ] ℂ) (ν : R2) (hν : ‖ν‖ = 1) :
    ‖L ν‖ ^ 2 ≤ ‖L (EuclideanSpace.single 0 1)‖ ^ 2 + ‖L (EuclideanSpace.single 1 1)‖ ^ 2 := by
  have hdec : ν = ν 0 • EuclideanSpace.single 0 (1 : ℝ) + ν 1 • EuclideanSpace.single 1 1 := by
    ext i; fin_cases i <;> simp
  have hsum : ν 0 ^ 2 + ν 1 ^ 2 = 1 := by
    have := EuclideanSpace.norm_sq_eq ν
    rw [hν, Fin.sum_univ_two] at this
    simpa [Real.norm_eq_abs, sq_abs] using this.symm
  set a := ‖L (EuclideanSpace.single 0 1)‖
  set b := ‖L (EuclideanSpace.single 1 1)‖
  have hle : ‖L ν‖ ≤ |ν 0| * a + |ν 1| * b := by
    calc ‖L ν‖ = ‖ν 0 • L (EuclideanSpace.single 0 1) + ν 1 • L (EuclideanSpace.single 1 1)‖ := by
          conv_lhs => rw [hdec]
          rw [map_add, map_smul, map_smul]
      _ ≤ _ := norm_add_le _ _
      _ = _ := by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have h0 : 0 ≤ ‖L ν‖ := norm_nonneg _
  have habs : |ν 0| ^ 2 + |ν 1| ^ 2 = 1 := by rw [sq_abs, sq_abs]; exact hsum
  nlinarith [sq_nonneg (|ν 0| * b - |ν 1| * a), abs_nonneg (ν 0), abs_nonneg (ν 1)]

lemma normal_norm (f : ℝ → ℝ) (s : ℝ) : ‖normal f s‖ = 1 := by
  have hpos : 0 < 1 + deriv f s ^ 2 := by positivity
  have hpt : ‖pt (deriv f s) (-1)‖ = Real.sqrt (1 + deriv f s ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp [pt, Fin.sum_univ_two]
    ring_nf
  rw [normal, norm_smul, hpt, arcDen, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hpos).ne'

theorem solution (f : ℝ → ℝ) (hf : IsBC1Alpha 1 f) (s0 δ : ℝ) (hδ : 0 < δ)
    (D0 : Set R2) (hD0 : Metric.ball (gpt f s0) (2 * δ) ∩ Dminus f ⊆ D0)
    (c : ℝ) (hc : c ≠ 0) :
    ∀ C : ℝ, ∃ j : ℕ, 1 ≤ j ∧ ENNReal.ofReal C <
      h1Norm D0 (fun x => (c : ℂ) * Phi 0 x (gpt f s0 - (δ / (j : ℝ)) • normal f s0)) := by
  intro C
  have hcpos : 0 < |c| := abs_pos.mpr hc
  obtain ⟨j, hj, hblow⟩ := dipole_l2_blowup f hf s0 δ hδ D0 hD0 (C / |c|)
  refine ⟨j, hj, ?_⟩
  set z := gpt f s0 - (δ / (j : ℝ)) • normal f s0
  set n := normal f s0
  have hn1 : ‖n‖ = 1 := normal_norm f s0
  -- pointwise: `|c ∂ₙΦ₀|² ≤ |∂₁(cΦ₀)|² + |∂₂(cΦ₀)|²` off the source point
  have hae : ∀ᵐ x ∂(volume.restrict D0), x ≠ z := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
    exact nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans (measure_singleton z).le)
  have hpt : ∀ᵐ x ∂(volume.restrict D0),
      ‖(c : ℂ) * dipoleSource 0 z n x‖ₑ ^ (2 : ℝ) ≤
        ‖(c : ℂ) * Phi 0 x z‖ₑ ^ 2 +
        ‖fderiv ℝ (fun x => (c : ℂ) * Phi 0 x z) x (EuclideanSpace.single 0 1)‖ₑ ^ 2 +
        ‖fderiv ℝ (fun x => (c : ℂ) * Phi 0 x z) x (EuclideanSpace.single 1 1)‖ₑ ^ 2 := by
    filter_upwards [hae] with x hx
    have hd : fderiv ℝ (fun x => (c : ℂ) * Phi 0 x z) x =
        (c : ℂ) • fderiv ℝ (fun x' => Phi 0 x' z) x :=
      fderiv_const_mul (phi0_differentiableAt z x hx) _
    rw [hd]
    have key := clm_unit_sq_le ((c : ℂ) • fderiv ℝ (fun x' => Phi 0 x' z) x) n hn1
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at key ⊢
    rw [ENNReal.rpow_two]
    simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ ‖(c : ℂ) * Phi 0 x z‖ ^ 2 := by positivity
    unfold dipoleSource
    linarith
  -- integrate
  have hL2 : ‖(c : ℂ)‖ₑ * l2Norm D0 (dipoleSource 0 z n) ≤
      h1Norm D0 (fun x => (c : ℂ) * Phi 0 x z) := by
    unfold l2Norm h1Norm
    rw [← eLpNorm_const_smul, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Pi.smul_apply, smul_eq_mul]
    exact ENNReal.rpow_le_rpow (lintegral_mono_ae hpt) (by norm_num)
  have hcn : ‖(c : ℂ)‖ₑ = ENNReal.ofReal |c| := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  have hlt : ENNReal.ofReal |c| * ENNReal.ofReal (C / |c|) <
      ENNReal.ofReal |c| * l2Norm D0 (dipoleSource 0 z n) :=
    ENNReal.mul_lt_mul_right (by simpa using hcpos) ENNReal.ofReal_ne_top hblow
  have heq : ENNReal.ofReal |c| * ENNReal.ofReal (C / |c|) = ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul hcpos.le, mul_div_cancel₀ _ hcpos.ne']
  rw [← heq]
  exact hlt.trans_le (hcn ▸ hL2)
