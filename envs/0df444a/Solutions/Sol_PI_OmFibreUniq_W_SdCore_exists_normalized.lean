-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdCore.exists_normalized
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:01:05.468714+00:00
-- url     : https://prove2.me/submissions/136714f8-8087-4d2f-a4d1-b10857da3daa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter
open PI.VolStabSW.SdUniqW
open scoped ENNReal
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
namespace PI.OmFibreUniq.W.SdCore
theorem _root_.solution (μ0 : Measure V) [μ0.IsAddHaarMeasure] (A B : ℕ → Set V)
    (hAc : ∀ k, IsCompact (A k)) (hBc : ∀ k, IsCompact (B k)) (hAo : IsOpen (A 0))
    (hBo : IsOpen (B 0)) (hA0 : (A 0).Nonempty) (hB0 : (B 0).Nonempty)
    (hconst : ∀ k, μ0 (A k) * μ0 (B k) = μ0 (A 0) * μ0 (B 0)) :
    ∃ μ : Measure V, μ.IsAddHaarMeasure ∧ ∀ k, μ.real (A k) * μ.real (B k) = 1 := by
  have ha0 : μ0 (A 0) ≠ 0 := (hAo.measure_pos μ0 hA0).ne'
  have hb0 : μ0 (B 0) ≠ 0 := (hBo.measure_pos μ0 hB0).ne'
  have hat : μ0 (A 0) ≠ ⊤ := (hAc 0).measure_lt_top.ne
  have hbt : μ0 (B 0) ≠ ⊤ := (hBc 0).measure_lt_top.ne
  set c : ℝ := (μ0 (A 0) * μ0 (B 0)).toReal with hc
  have hcpos : 0 < c := ENNReal.toReal_pos (mul_ne_zero ha0 hb0) (ENNReal.mul_ne_top hat hbt)
  set s : ℝ := Real.sqrt c with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hcpos
  have hss : s * s = c := Real.mul_self_sqrt hcpos.le
  set r : ℝ≥0∞ := ENNReal.ofReal (1 / s) with hr
  have hr0 : r ≠ 0 := by
    rw [hr, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hrt : r ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨r • μ0, Measure.IsAddHaarMeasure.smul (μ := μ0) hr0 hrt, fun k => ?_⟩
  have hk : (μ0 (A k)).toReal * (μ0 (B k)).toReal = c := by
    rw [← ENNReal.toReal_mul, hconst k]
  simp only [Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [hr, ENNReal.toReal_ofReal (by positivity)]
  calc 1 / s * (μ0 (A k)).toReal * (1 / s * (μ0 (B k)).toReal)
      = ((μ0 (A k)).toReal * (μ0 (B k)).toReal) / (s * s) := by field_simp
    _ = 1 := by rw [hk, hss, div_self hcpos.ne']
end PI.OmFibreUniq.W.SdCore
