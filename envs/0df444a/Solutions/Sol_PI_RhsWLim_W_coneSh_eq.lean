-- Prove2me | solution 1 for PI.RhsWLim.W.coneSh_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:24:52.729465+00:00
-- url     : https://prove2.me/submissions/0f047342-4020-4d1d-9721-0efabc844e43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_OrbitPushV
import Theorems.Thm_PI_RhsWLim_W_qf_smul

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
theorem _root_.solution {T' : ℝ} (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) :
    coneSh k T' E = {p | qf k p < 0 ∧ 1 < tau k T' p ∧ tau k T' p < 2 ∧ (tau k T' p)⁻¹ • p ∈ E} := by
  ext p
  constructor
  · rintro ⟨⟨v, t⟩, ⟨⟨hvE, hvS⟩, ht1, ht2⟩, rfl⟩
    have hv : qf k v = -T' := hvS
    have hq : qf k (t • v) = -(t ^ 2 * T') := by rw [qf_smul, hv]; ring
    have htau : tau k T' (t • v) = t := by
      unfold tau
      rw [hq, neg_neg, mul_div_assoc, div_self hT'.ne', mul_one, Real.sqrt_sq (by have : 1 < t := ht1; linarith)]
    have ht1' : 1 < t := ht1
    have hpos : 0 < t ^ 2 * T' := mul_pos (pow_pos (by linarith) 2) hT'
    refine ⟨by rw [hq]; linarith, by rw [htau]; exact ht1, by rw [htau]; exact ht2, ?_⟩
    rw [htau, smul_smul, inv_mul_cancel₀ (by linarith : t ≠ 0), one_smul]
    exact hvE
  · rintro ⟨hneg, h1, h2, hE⟩
    have hq0 : qf k p ≠ 0 := hneg.ne
    have ht2 : tau k T' p ^ 2 = -qf k p / T' := by
      unfold tau
      rw [Real.sq_sqrt (div_nonneg (by linarith) hT'.le)]
    refine ⟨((tau k T' p)⁻¹ • p, tau k T' p), ⟨⟨hE, ?_⟩, h1, h2⟩, ?_⟩
    · show qf k ((tau k T' p)⁻¹ • p) = -T'
      rw [qf_smul, inv_pow, ht2, inv_div, div_mul_eq_mul_div, div_eq_iff (neg_ne_zero.2 hq0)]
      ring
    · show tau k T' p • ((tau k T' p)⁻¹ • p) = p
      rw [smul_smul, mul_inv_cancel₀ (by linarith : tau k T' p ≠ 0), one_smul]
end PI.RhsWLim.W
