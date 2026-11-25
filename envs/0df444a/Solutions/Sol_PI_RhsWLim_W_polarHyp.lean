-- Prove2me | solution 1 for PI.RhsWLim.W.polarHyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:33:39.009979+00:00
-- url     : https://prove2.me/submissions/a608bd0d-65a6-4cbf-8e70-03169e898378

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_PolarHyp
import Theorems.Thm_PI_RhsWLim_W_PH_lintegral_norm_ck
import Theorems.Thm_PI_RhsWLim_W_PH_shift_pi
import Theorems.Thm_PI_RhsWLim_W_PH_lintegral_polar
import Theorems.Thm_PI_RhsWLim_W_PH_subst_R

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim PH
namespace PI.RhsWLim.W
theorem _root_.solution : PolarHyp := by
  intro k T T' hk hT hT' g hg
  have hs0 : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hTT : 0 < T * T' := mul_pos hT hT'
  set H : ℝ → ℝ≥0∞ := fun ρ => ∫⁻ θ in Ioc 0 (2 * Real.pi),
    g ρ ((Real.sqrt (ρ ^ 2 + T') : ℂ) * Complex.exp (θ * Complex.I)) with hHdef
  have hH : Measurable H := by
    have hm : Measurable fun p : ℝ × ℝ =>
        g p.1 ((Real.sqrt (p.1 ^ 2 + T') : ℂ) * Complex.exp (p.2 * Complex.I)) :=
      hg.comp (measurable_fst.prodMk (by fun_prop))
    exact hm.lintegral_prod_right'
  have eL : hypMeas k T' (fun v => g ‖(WithLp.equiv 2 (Fin k → ℂ)).symm v.1‖ v.2) =
      1 / 2 * ∫⁻ y : EuclideanSpace ℂ (Fin k), H ‖y‖ := rfl
  rw [eL, lintegral_norm_ck k hk H hH]
  set Hh : ℝ → ℝ≥0∞ := fun R => ∫⁻ θ in Ioc 0 (2 * Real.pi),
    g (Real.sqrt ((R ^ 2 - T * T') / T)) (((R / Real.sqrt T : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) with hHh
  set wR : ℝ → ℝ := fun R => if T * T' ≤ R ^ 2 then (R ^ 2 - T * T') ^ (k - 1) else 0 with hwR
  have hw : Measurable fun ζ : ℂ => zWeight k T T' ζ := by
    unfold zWeight
    exact Measurable.ite (measurableSet_le measurable_const Complex.continuous_normSq.measurable)
      ((Complex.continuous_normSq.sub continuous_const).pow _).measurable measurable_const
  have hΨ : Measurable fun ζ : ℂ => ENNReal.ofReal (zWeight k T T' ζ) *
      g (Real.sqrt ((Complex.normSq ζ - T * T') / T)) (-(ζ / (Real.sqrt T : ℂ))) := by
    refine (ENNReal.measurable_ofReal.comp hw).mul (hg.comp (Measurable.prodMk ?_ ?_))
    · exact (Real.continuous_sqrt.comp ((Complex.continuous_normSq.sub continuous_const).div_const T)).measurable
    · exact (continuous_id.div_const _).neg.measurable
  rw [lintegral_polar _ hΨ]
  have eP : ∀ R ∈ Ioi (0 : ℝ), ENNReal.ofReal R * ∫⁻ φ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal (zWeight k T T' (R * (Real.cos φ + Real.sin φ * Complex.I))) *
        g (Real.sqrt ((Complex.normSq (R * (Real.cos φ + Real.sin φ * Complex.I)) - T * T') / T))
          (-((R * (Real.cos φ + Real.sin φ * Complex.I)) / (Real.sqrt T : ℂ))) =
      ENNReal.ofReal R * (ENNReal.ofReal (wR R) * Hh R) := by
    intro R hR
    have hn : ∀ φ : ℝ, Complex.normSq (R * (Real.cos φ + Real.sin φ * Complex.I)) = R ^ 2 := by
      intro φ
      rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_add_mul_I, Real.cos_sq_add_sin_sq]; ring
    have hc : ∀ φ : ℝ, -((R * (Real.cos φ + Real.sin φ * Complex.I)) / (Real.sqrt T : ℂ)) =
        ((R / Real.sqrt T : ℝ) : ℂ) * Complex.exp (((φ + Real.pi : ℝ) : ℂ) * Complex.I) := by
      intro φ
      rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_mul_I, Complex.exp_pi_mul_I]
      push_cast
      ring
    have hz : ∀ φ : ℝ, zWeight k T T' (R * (Real.cos φ + Real.sin φ * Complex.I)) = wR R := by
      intro φ; simp only [zWeight, hn, hwR]
    simp_rw [hn, hc, hz]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 2
    exact shift_pi (fun θ => g (Real.sqrt ((R ^ 2 - T * T') / T))
      (((R / Real.sqrt T : ℝ) : ℂ) * Complex.exp (θ * Complex.I)))
  rw [setLIntegral_congr_fun measurableSet_Ioi eP]
  rw [subst_R T T' hT hT' (fun R => ENNReal.ofReal R * (ENNReal.ofReal (wR R) * Hh R)) (fun R hR => by
      have h : ¬ T * T' ≤ R ^ 2 := by
        have := (Real.lt_sqrt hR.1.le).1 hR.2
        linarith
      simp [hwR, h])]
  have eS : ∀ ρ ∈ Ioi (0 : ℝ), ENNReal.ofReal (|T * ρ / Real.sqrt (T * (ρ ^ 2 + T'))|) *
      (ENNReal.ofReal (Real.sqrt (T * (ρ ^ 2 + T'))) *
        (ENNReal.ofReal (wR (Real.sqrt (T * (ρ ^ 2 + T')))) * Hh (Real.sqrt (T * (ρ ^ 2 + T'))))) =
      ENNReal.ofReal (T ^ k) * (ENNReal.ofReal (ρ ^ (2 * k - 1)) * H ρ) := by
    intro ρ hρ
    have hρ0 : (0 : ℝ) < ρ := hρ
    have hp : 0 < T * (ρ ^ 2 + T') := by positivity
    set F := Real.sqrt (T * (ρ ^ 2 + T')) with hF
    have hF0 : 0 < F := Real.sqrt_pos.2 hp
    have hF2 : F ^ 2 = T * (ρ ^ 2 + T') := Real.sq_sqrt hp.le
    have hwF : wR F = (T * ρ ^ 2) ^ (k - 1) := by
      have hle : T * T' ≤ F ^ 2 := by
        rw [hF2]; have : 0 ≤ T * ρ ^ 2 := by positivity
        linarith
      simp only [hwR]
      rw [if_pos hle, hF2]
      congr 1; ring
    have hHF : Hh F = H ρ := by
      have h1 : Real.sqrt ((F ^ 2 - T * T') / T) = ρ := by
        rw [hF2, show (T * (ρ ^ 2 + T') - T * T') / T = ρ ^ 2 by field_simp; ring, Real.sqrt_sq hρ0.le]
      have h2 : F / Real.sqrt T = Real.sqrt (ρ ^ 2 + T') := by
        rw [hF, Real.sqrt_mul hT.le, mul_div_cancel_left₀ _ hs0.ne']
      simp only [hHh, hHdef]
      rw [h1, h2]
    rw [hwF, hHF, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity), ← mul_assoc,
      ← ENNReal.ofReal_mul (pow_nonneg hT.le k)]
    congr 2
    rw [abs_of_pos (by positivity), div_mul_cancel₀ _ hF0.ne']
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, Nat.add_sub_cancel]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi eS, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have h12 : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [one_div, one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  rw [h12, ← ENNReal.ofReal_mul (by norm_num)]
  congr 2
  field_simp
end PI.RhsWLim.W
