-- Prove2me | solution 1 for PI.RhsWLim.W.radial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:54:49.669136+00:00
-- url     : https://prove2.me/submissions/ccbf024d-8739-47e0-abb9-a8f5c2946698

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushR
import Theorems.Thm_PI_RhsWLim_W_coneSh_eq
import Theorems.Thm_PI_RhsWLim_W_measurableSet_coneSh
import Theorems.Thm_PI_RhsWLim_W_slice_mem


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
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W
open PI.RhsWLim
variable {k : ℕ}
namespace PI.RhsWLim.W
theorem _root_.solution {T' : ℝ} (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) (hE : MeasurableSet E) (y : Fin k → ℂ)
    (θ : ℝ) :
    ∫⁻ R in Set.Ioi (0 : ℝ), ENNReal.ofReal R *
        (coneSh k T' E).indicator 1 (y, (R : ℂ) * Complex.exp (θ * Complex.I)) =
      ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal (T' * t) * E.indicator 1 (hq k T' (t⁻¹ • y) θ) := by
  set a := ∑ i, Complex.normSq (y i) with ha_def
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hS := measurableSet_coneSh hT' hE
  set g : ℝ → ℝ≥0∞ := fun R => ENNReal.ofReal R *
    (coneSh k T' E).indicator 1 (y, (R : ℂ) * Complex.exp (θ * Complex.I)) with hgdef
  have hsupp : ((Set.Ioi (0 : ℝ)).indicator g).support ⊆ phiR a T' '' Set.Ioo 1 2 := by
    intro R hR
    rw [Function.mem_support] at hR
    have hR0 : R ∈ Set.Ioi (0 : ℝ) := by
      by_contra h
      exact hR (Set.indicator_of_notMem h _)
    rw [Set.indicator_of_mem hR0] at hR
    have hR0' : 0 < R := hR0
    have hmem : (y, (R : ℂ) * Complex.exp (θ * Complex.I)) ∈ coneSh k T' E := by
      by_contra h
      apply hR
      simp only [hgdef, Set.indicator_of_notMem h, mul_zero]
    rw [coneSh_eq hT'] at hmem
    obtain ⟨hneg, h1, h2, -⟩ := hmem
    refine ⟨tau k T' (y, (R : ℂ) * Complex.exp (θ * Complex.I)), ⟨h1, h2⟩, ?_⟩
    have hqv : qf k (y, (R : ℂ) * Complex.exp (θ * Complex.I)) = a - R ^ 2 := by
      unfold qf
      simp only
      rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq (Complex.exp _),
        Complex.norm_exp_ofReal_mul_I, ← ha_def]
      ring
    have htau2 : tau k T' (y, (R : ℂ) * Complex.exp (θ * Complex.I)) ^ 2 = (R ^ 2 - a) / T' := by
      unfold tau
      rw [Real.sq_sqrt (div_nonneg (by linarith) hT'.le), hqv]
      ring
    unfold phiR
    rw [htau2, div_mul_cancel₀ _ hT'.ne', show a + (R ^ 2 - a) = R ^ 2 by ring, Real.sqrt_sq hR0'.le]
  rw [← lintegral_indicator measurableSet_Ioi, ← setLIntegral_eq_of_support_subset hsupp]
  have hpos : ∀ t : ℝ, 0 < t → 0 < a + t ^ 2 * T' := fun t ht =>
    add_pos_of_nonneg_of_pos ha (mul_pos (pow_pos ht 2) hT')
  have hderiv : ∀ t ∈ Set.Ioo (1 : ℝ) 2, HasDerivWithinAt (phiR a T')
      (2 * t * T' / (2 * Real.sqrt (a + t ^ 2 * T'))) (Set.Ioo 1 2) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 : HasDerivAt (fun t => a + t ^ 2 * T') (2 * t * T') t := by
      have := ((hasDerivAt_pow 2 t).mul_const T').const_add a
      exact this.congr_deriv (by ring)
    exact (h1.sqrt (hpos t ht0).ne').hasDerivWithinAt
  have hinj : Set.InjOn (phiR a T') (Set.Ioo 1 2) := by
    intro t1 h1 t2 h2 he
    have h10 : 0 < t1 := by linarith [h1.1]
    have h20 : 0 < t2 := by linarith [h2.1]
    unfold phiR at he
    rw [Real.sqrt_inj (hpos t1 h10).le (hpos t2 h20).le] at he
    have e2 : t1 ^ 2 = t2 ^ 2 := mul_right_cancel₀ hT'.ne' (by linarith)
    exact (pow_left_inj₀ h10.le h20.le two_ne_zero).1 e2
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have ht0 : 0 < t := by linarith [ht.1]
  have hφpos : 0 < Real.sqrt (a + t ^ 2 * T') := Real.sqrt_pos.2 (hpos t ht0)
  have hφ : phiR a T' t = Real.sqrt (a + t ^ 2 * T') := rfl
  rw [Set.indicator_of_mem (show phiR a T' t ∈ Set.Ioi (0 : ℝ) from hφ ▸ hφpos)]
  have hm := slice_mem hT' E y θ t ht0
  have hfac : ENNReal.ofReal |2 * t * T' / (2 * Real.sqrt (a + t ^ 2 * T'))| *
      ENNReal.ofReal (phiR a T' t) = ENNReal.ofReal (T' * t) := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (div_pos (mul_pos (mul_pos two_pos ht0) hT')
      (mul_pos two_pos hφpos)), hφ]
    congr 1
    field_simp
  by_cases hE' : hq k T' (t⁻¹ • y) θ ∈ E
  · rw [Set.indicator_of_mem hE']
    simp only [hgdef]
    rw [Set.indicator_of_mem (hm.2 ⟨ht.1, ht.2, hE'⟩)]
    simp only [Pi.one_apply, mul_one]
    exact hfac
  · rw [Set.indicator_of_notMem hE']
    simp only [hgdef]
    rw [Set.indicator_of_notMem (fun h => hE' (hm.1 h).2.2)]
    simp
end PI.RhsWLim.W
