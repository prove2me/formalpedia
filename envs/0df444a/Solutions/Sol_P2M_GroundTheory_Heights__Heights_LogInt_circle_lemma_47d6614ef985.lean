-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_circle_lemma_47d6614ef985
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:24:10.614113+00:00
-- url     : https://prove2.me/submissions/95687b0b-d57c-4534-87e6-564e384860b6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_lintegral_abs_log_circle_le_d71509c99c48
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_countable_eval_circleMap_eq_zero_e15f1f0a7180
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LogInt_setLIntegral_rot_7dac8de6a7df

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
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution {V : Type*} [MeasurableSpace V] (μ : Measure V) [SFinite μ]
    (S : Set V) (hS : MeasurableSet S) (hSfin : μ S ≠ ⊤)
    (R : ℝ → V → V) (hR : Measurable (Function.uncurry R))
    (hpres : ∀ θ, MeasurePreserving (R θ) μ μ) (hinv : ∀ θ, R θ ⁻¹' S = S)
    (F : V → ℂ) (hF : Measurable F) (c : ℕ → V → ℂ) (D d0 : ℕ) (hd0 : d0 ≤ D)
    (hexp : ∀ θ u, F (R θ u) = ∑ d ∈ Finset.range (D + 1), c d u * circleMap 0 1 θ ^ d)
    (hint : IntegrableOn (fun u => Real.log ‖c d0 u‖) S μ)
    (hnz : ∀ᵐ u ∂(μ.restrict S), c d0 u ≠ 0)
    (M : ℝ) (hM : ∀ u ∈ S, ‖F u‖ ≤ M) :
    IntegrableOn (fun u => Real.log ‖F u‖) S μ ∧ ∀ᵐ u ∂(μ.restrict S), F u ≠ 0 := by
  classical

  set P : V → Polynomial ℂ := fun u =>
    ∑ d ∈ Finset.range (D + 1), Polynomial.C (c d u) * Polynomial.X ^ d with hPdef
  have hPeval : ∀ θ u, (P u).eval (circleMap 0 1 θ) = F (R θ u) := by
    intro θ u
    rw [hexp, hPdef, Polynomial.eval_finsetSum]
    simp
  have hPcoeff : ∀ u, (P u).coeff d0 = c d0 u := by
    intro u
    rw [hPdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single d0]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hd0)) h
  have hPdeg : ∀ u, (P u).natDegree ≤ D := by
    intro u
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd))
  have hRS : ∀ θ u, u ∈ S → R θ u ∈ S := by
    intro θ u hu
    have : u ∈ R θ ⁻¹' S := by rw [hinv θ]; exact hu
    exact this
  have hFm : Measurable fun u => Real.log ‖F u‖ := Real.measurable_log.comp hF.norm
  refine ⟨⟨hFm.aestronglyMeasurable, ?_⟩, ?_⟩
  ·
    set K : ℝ := 4 * Real.pi * Real.log (max M 1) + 2 * Real.pi * D * Real.log 2 with hK
    have hbound : ∀ᵐ u ∂(μ.restrict S),
        ∫⁻ θ in Ioc 0 (2 * Real.pi), ‖Real.log ‖F (R θ u)‖‖ₑ ≤
          ENNReal.ofReal (K + 2 * Real.pi * |Real.log ‖c d0 u‖|) := by
      filter_upwards [hnz, ae_restrict_mem hS] with u hu huS
      have := lintegral_abs_log_circle_le (P u) D d0 M (hPdeg u) (by rw [hPcoeff]; exact hu)
        (fun θ => by rw [hPeval]; exact hM _ (hRS θ u huS))
      have e : (fun θ => ‖Real.log ‖F (R θ u)‖‖ₑ) =
          fun θ => ‖Real.log ‖(P u).eval (circleMap 0 1 θ)‖‖ₑ := by
        funext θ; rw [hPeval]
      rw [e, ← hPcoeff u]
      exact this
    have hrot := setLIntegral_rot μ S hS R hR hpres hinv (fun u => ‖Real.log ‖F u‖‖ₑ)
      (hFm.enorm)
    have hKint : Integrable (fun u => K + 2 * Real.pi * |Real.log ‖c d0 u‖|) (μ.restrict S) := by
      have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hSfin
      exact (integrable_const K).add (hint.abs.const_mul _)
    have hlt : ∫⁻ u in S, (∫⁻ θ in Ioc 0 (2 * Real.pi), ‖Real.log ‖F (R θ u)‖‖ₑ) ∂μ < ⊤ :=
      (lintegral_mono_ae hbound).trans_lt hKint.lintegral_lt_top
    rw [← hrot] at hlt
    have h2 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have := (ENNReal.mul_lt_top_iff.mp hlt)
    rcases this with ⟨-, h⟩ | h | h
    · exact h
    · exact absurd h h2
    · change ∫⁻ u in S, ‖Real.log ‖F u‖‖ₑ ∂μ < ⊤
      rw [h]; exact ENNReal.zero_lt_top
  ·
    have hZ : MeasurableSet {u | F u = 0} := hF (measurableSet_singleton 0)
    have hrot := setLIntegral_rot μ S hS R hR hpres hinv ({u | F u = 0}.indicator 1)
      (measurable_one.indicator hZ)
    have hinner : ∀ᵐ u ∂(μ.restrict S),
        ∫⁻ θ in Ioc 0 (2 * Real.pi), {u | F u = 0}.indicator (1 : V → ENNReal) (R θ u) = 0 := by
      filter_upwards [hnz] with u hu
      have hPu : P u ≠ 0 := fun h => hu (by rw [← hPcoeff, h]; simp)
      have hc := countable_eval_circleMap_eq_zero (P u) hPu
      have : (fun θ => {u | F u = 0}.indicator (1 : V → ENNReal) (R θ u)) =
          {θ : ℝ | (P u).eval (circleMap 0 1 θ) = 0}.indicator 1 := by
        funext θ
        simp only [Set.indicator, mem_ofPred_eq, hPeval, Pi.one_apply]
      rw [this, lintegral_indicator_one hc.measurableSet]
      exact hc.measure_zero _
    have h0 : ∫⁻ u in S, (∫⁻ θ in Ioc 0 (2 * Real.pi),
        {u | F u = 0}.indicator (1 : V → ENNReal) (R θ u)) ∂μ = 0 := by
      rw [lintegral_congr_ae hinner, lintegral_zero]
    rw [h0, lintegral_indicator_one hZ] at hrot
    have h2 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have h3 := (mul_eq_zero.mp hrot).resolve_left h2
    rw [ae_iff]
    simpa using h3
end GroundTheory.Heights₂.Heights.LogInt
