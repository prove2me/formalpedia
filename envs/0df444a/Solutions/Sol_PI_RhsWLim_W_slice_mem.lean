-- Prove2me | solution 1 for PI.RhsWLim.W.slice_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:29:38.381644+00:00
-- url     : https://prove2.me/submissions/8c3fe2e3-b005-43e4-a46f-6f83e8c558ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushV
import Theorems.Thm_PI_RhsWLim_W_normSq_real_smul
import Theorems.Thm_PI_RhsWLim_W_coneSh_eq

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
theorem _root_.solution {T' : ℝ} (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) (y : Fin k → ℂ) (θ t : ℝ) (ht : 0 < t) :
    (y, ((phiR (∑ i, Complex.normSq (y i)) T' t : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) ∈ coneSh k T' E ↔
      (1 < t ∧ t < 2 ∧ hq k T' (t⁻¹ • y) θ ∈ E) := by
  set a := ∑ i, Complex.normSq (y i) with ha_def
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  set φ := phiR a T' t with hφdef
  have hφ0 : 0 ≤ φ := Real.sqrt_nonneg _
  have hφ2 : φ ^ 2 = a + t ^ 2 * T' := Real.sq_sqrt (by positivity)
  have hqv : qf k (y, (φ : ℂ) * Complex.exp (θ * Complex.I)) = -(t ^ 2 * T') := by
    unfold qf
    simp only
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq (Complex.exp _),
      Complex.norm_exp_ofReal_mul_I, ← ha_def]
    linear_combination (-1 : ℝ) * hφ2
  have htau : tau k T' (y, (φ : ℂ) * Complex.exp (θ * Complex.I)) = t := by
    unfold tau
    rw [hqv, neg_neg, mul_div_assoc, div_self hT'.ne', mul_one, Real.sqrt_sq ht.le]
  have hsc : (t⁻¹ : ℝ) • ((y, (φ : ℂ) * Complex.exp (θ * Complex.I)) : (Fin k → ℂ) × ℂ) =
      hq k T' (t⁻¹ • y) θ := by
    unfold hq
    have hs : ∑ i, Complex.normSq ((t⁻¹ • y) i) = t⁻¹ ^ 2 * a := by
      simp only [Pi.smul_apply, normSq_real_smul, ← Finset.mul_sum, ha_def]
    have hr : Real.sqrt (∑ i, Complex.normSq ((t⁻¹ • y) i) + T') = t⁻¹ * φ := by
      rw [hs, show t⁻¹ ^ 2 * a + T' = (t⁻¹ * φ) ^ 2 by
        rw [mul_pow, hφ2]; field_simp]
      exact Real.sqrt_sq (mul_nonneg (inv_nonneg.2 ht.le) hφ0)
    rw [hr, Prod.smul_mk, Complex.real_smul]
    push_cast
    ring_nf
  rw [coneSh_eq hT']
  simp only [Set.mem_ofPred_eq]
  rw [htau, hsc]
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, h2, h3⟩
    rw [hqv]
    have : 0 < t ^ 2 * T' := by positivity
    linarith
end PI.RhsWLim.W
