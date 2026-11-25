-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_lintegral_ballSet_neg_log_sqNorm_45f854ab08a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:27:39.627728+00:00
-- url     : https://prove2.me/submissions/cecd798f-5782-4adf-a198-deeda46b9548

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanDisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanSlice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_singleton_zero_b8b7cba0e078
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_pos_of_ne_zero_64c6d51818d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_measurableSet_ballSet_d8b80531e855
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_measurable_sqNorm_950a20036208
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_sqNorm_nonneg_b8444e370306
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_volume_ballSet_af9c6325d276


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set Real
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution (m : ℕ) :
    ∫⁻ x in ballSet (m + 1) 1, ENNReal.ofReal (-log (sqNorm x)) =
      ENNReal.ofReal (1 / (m + 1)) * volume (ballSet (m + 1) 1) := by
  set B := ballSet (m + 1) 1 with hB
  have hmeas : Measurable fun x : Fin (m + 1) → ℂ => -log (sqNorm x) :=
    (measurable_sqNorm _).log.neg
  have hnn : 0 ≤ᵐ[volume.restrict B] fun x => -log (sqNorm x) := by
    refine (ae_restrict_iff' (measurableSet_ballSet _ _)).mpr (Filter.Eventually.of_forall ?_)
    intro x hx
    simp only [Pi.zero_apply]
    rw [neg_nonneg]
    exact log_nonpos (sqNorm_nonneg x) (le_of_lt hx)
  rw [lintegral_eq_lintegral_meas_lt _ hnn hmeas.aemeasurable]
  have hlev : ∀ t ∈ Ioi (0 : ℝ), (volume.restrict B) {x | t < -log (sqNorm x)} =
      ENNReal.ofReal (exp (-((m + 1 : ℕ) : ℝ) * t)) * volume B := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    rw [Measure.restrict_apply (measurableSet_lt measurable_const hmeas)]
    have he : exp (-t) < 1 := by
      have := exp_lt_exp.mpr (show -t < 0 by linarith)
      rwa [exp_zero] at this
    have hsub1 : {x | t < -log (sqNorm x)} ∩ B ⊆ ballSet (m + 1) (exp (-t)) := by
      intro x ⟨hx1, _⟩
      simp only [mem_ofPred_eq] at hx1
      have hs : 0 < sqNorm x := by
        rcases (sqNorm_nonneg x).lt_or_eq with h | h
        · exact h
        · rw [← h, log_zero] at hx1; linarith
      simp only [ballSet, mem_ofPred_eq]
      rw [← log_lt_iff_lt_exp hs]
      linarith
    have hsub2 : ballSet (m + 1) (exp (-t)) ⊆ ({x | t < -log (sqNorm x)} ∩ B) ∪ {0} := by
      intro x hx
      by_cases h0 : x = 0
      · exact Or.inr h0
      · left
        have hs := sqNorm_pos_of_ne_zero h0
        simp only [ballSet, mem_ofPred_eq] at hx
        refine ⟨?_, ?_⟩
        · simp only [mem_ofPred_eq]
          have := (log_lt_iff_lt_exp hs).mpr hx
          linarith
        · simp only [hB, ballSet, mem_ofPred_eq]
          linarith
    have heq : volume ({x | t < -log (sqNorm x)} ∩ B) = volume (ballSet (m + 1) (exp (-t))) := by
      refine le_antisymm (measure_mono hsub1) ?_
      refine (measure_mono hsub2).trans ((measure_union_le _ _).trans ?_)
      rw [volume_singleton_zero, add_zero]
    rw [heq, volume_ballSet (exp_pos _), ← exp_nat_mul]
    have : ((m + 1 : ℕ) : ℝ) * -t = -((m + 1 : ℕ) : ℝ) * t := by ring
    rw [this]
  rw [setLIntegral_congr_fun measurableSet_Ioi hlev, lintegral_mul_const _
    (Measurable.ennreal_ofReal (by fun_prop))]
  congr 1
  have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal (exp_neg_integrableOn_Ioi 0 hpos)
    (Filter.Eventually.of_forall fun t => (exp_pos _).le)]
  have := integral_exp_mul_Ioi (a := -((m + 1 : ℕ) : ℝ)) (by linarith) 0
  simp only [mul_zero, exp_zero] at this
  rw [this]
  congr 1
  push_cast
  field_simp
end GroundTheory.Heights₂.Heights.SphereMean
