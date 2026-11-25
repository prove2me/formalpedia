-- Prove2me | solution 1 for PositivityTheory.RgJS.LandauNonnegativeDirichletSeries.summable_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:54:07.851082+00:00
-- url     : https://prove2.me/submissions/270bb432-9fda-45c8-9f9d-d94e082d25a7

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_LandauIteratedDerivatives_LandauL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
namespace PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
theorem _root_.solution {ι : Type} (b μ : ι → ℝ) (hb : ∀ j, 0 ≤ b j) (hμ : ∀ j, 0 ≤ μ j) (a : ℝ)
    (h : ∀ σ : ℝ, a < σ → Summable (fun j => b j * Real.exp (-(μ j) * σ))) (n : ℕ) (σ : ℝ) (hσ : a < σ) :
    Summable (fun j => b j * μ j ^ n * Real.exp (-(μ j) * σ)) := by
  set δ := (σ - a) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have h1 := (h (σ - δ) (by rw [hδ]; linarith)).mul_left ((n.factorial : ℝ) / δ ^ n)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) h1
  · have := hb j; have := hμ j; positivity
  · have h2 := Real.pow_div_factorial_le_exp (μ j * δ) (mul_nonneg (hμ j) hδ0.le) n
    have hf : (0:ℝ) < n.factorial := by positivity
    have h3 : μ j ^ n ≤ (n.factorial : ℝ) / δ ^ n * Real.exp (μ j * δ) := by
      rw [div_le_iff₀ hf, mul_pow] at h2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith
    have h4 : Real.exp (-(μ j) * (σ - δ)) = Real.exp (μ j * δ) * Real.exp (-(μ j) * σ) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h4]
    have h5 : 0 ≤ b j * Real.exp (-(μ j) * σ) := mul_nonneg (hb j) (Real.exp_pos _).le
    calc b j * μ j ^ n * Real.exp (-(μ j) * σ) = μ j ^ n * (b j * Real.exp (-(μ j) * σ)) := by ring
      _ ≤ ((n.factorial : ℝ) / δ ^ n * Real.exp (μ j * δ)) * (b j * Real.exp (-(μ j) * σ)) :=
        mul_le_mul_of_nonneg_right h3 h5
      _ = _ := by ring
end PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
