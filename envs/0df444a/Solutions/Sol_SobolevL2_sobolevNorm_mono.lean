-- Prove2me | solution 1 for SobolevL2.sobolevNorm_mono
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T18:28:56.449597+00:00
-- url     : https://prove2.me/submissions/261acbe5-5a8f-49a9-a454-7151ac5e553a

import Mathlib
import Definitions.Def_SobolevL2_SobolevNorm

open MeasureTheory TemperedDistribution Filter Topology
open scoped ENNReal NNReal SchwartzMap FourierTransform LineDeriv BoundedContinuousFunction

set_option autoImplicit false

theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {s t : ℝ} (hts : t ≤ s) (u : 𝓢'(E, F)) :
    SobolevL2.sobolevNorm t u ≤ SobolevL2.sobolevNorm s u := by
  unfold SobolevL2.sobolevNorm
  refine le_iInf₂ fun f hf => ?_
  -- the symbol of `J^{t-s}`, bounded by `1` since `t - s ≤ 0`
  set g : E → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ ((t - s) / 2) : ℝ) : ℂ) with hg_def
  have hg₁ : g.HasTemperateGrowth := by rw [hg_def]; fun_prop
  have hgbound : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    have h' : (t - s) / 2 ≤ 0 := by linarith
    rw [hg_def]
    dsimp only
    rw [Complex.norm_real, Real.norm_eq_abs, abs_eq_self.mpr (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖]) h'
  set g' : E →ᵇ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup g hg₁.1.continuous 1 hgbound
  have hgmem : MemLp g ⊤ (volume : Measure E) := g'.memLp_top
  set G : Lp ℂ ⊤ (volume : Measure E) := hgmem.toLp g
  set h : Lp F 2 (volume : Measure E) := 𝓕⁻ (G • 𝓕 f)
  -- `J^t u = J^{t-s} (J^s u) = J^{t-s} f = h`
  have hJ : besselPotential E F t u = (h : 𝓢'(E, F)) := by
    have hsplit : besselPotential E F t u =
        besselPotential E F (t - s) (besselPotential E F s u) := by
      rw [besselPotential_besselPotential_apply, add_sub_cancel]
    rw [hsplit, hf, besselPotential, fourierMultiplierCLM_apply,
      Lp.fourier_toTemperedDistribution_eq, ← Lp.toTemperedDistribution_smul_eq (r := 2) hg₁ hgmem,
      Lp.fourierInv_toTemperedDistribution_eq]
  -- Plancherel and `‖g‖_∞ ≤ 1`
  have hG : ‖G‖ ≤ 1 := by
    rw [Lp.norm_toLp, eLpNorm_exponent_top]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (eLpNormEssSup_le_of_ae_bound (Eventually.of_forall hgbound))
  have hnorm : ‖h‖ ≤ ‖f‖ := by
    calc ‖h‖ = ‖G • 𝓕 f‖ := (Lp.fourierTransformₗᵢ E F).symm.norm_map _
      _ ≤ ‖G‖ * ‖𝓕 f‖ := Lp.norm_smul_le _ _
      _ ≤ 1 * ‖f‖ := by
        rw [Lp.norm_fourier_eq]
        exact mul_le_mul_of_nonneg_right hG (norm_nonneg _)
      _ = ‖f‖ := one_mul _
  have hnorm' : ‖h‖ₑ ≤ ‖f‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hnorm
  exact (iInf₂_le h hJ).trans hnorm'
