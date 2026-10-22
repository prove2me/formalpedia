-- Prove2me | solution 1 for SeqSocialLearning.Adequate.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:38:46.059396+00:00
-- url     : https://prove2.me/submissions/1e878e4e-4278-453e-9093-f16408059b4c

import Mathlib
import Definitions.Def_SeqSocialLearning_Adequate_Model

open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {Ω : Type*}
    [MetricSpace Ω] [CompleteSpace Ω] [TopologicalSpace.SeparableSpace Ω]
    [MeasurableSpace Ω] [BorelSpace Ω] [Nonempty Ω]
    (P : Measure (Measure Ω)) [IsProbabilityMeasure P]
    (hP : ∀ᵐ lam ∂P, IsProbabilityMeasure lam)
    (K : Set (Measure Ω)) (hK : MeasurableSet K) (hPK : 0 < P K) :
    (P[|K]).join ≪ P.join ∧
      ∀ᵐ ω ∂P.join, (P[|K]).join.rnDeriv P.join ω ≤ (P K)⁻¹ := by
  have hfin : IsFiniteMeasure P.join := by
    constructor
    rw [Measure.join_apply MeasurableSet.univ]
    have : ∫⁻ lam : Measure Ω, lam Set.univ ∂P = ∫⁻ _lam : Measure Ω, 1 ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hP] with lam hlam
      exact measure_univ
    rw [this]
    simp
  set r : NNReal := ((P K).toNNReal)⁻¹ with hr_def
  have hPKtop : P K ≠ ⊤ := measure_ne_top P K
  have hPK0 : (P K).toNNReal ≠ 0 := by
    rw [Ne, ENNReal.toNNReal_eq_zero_iff]; push Not; exact ⟨hPK.ne', hPKtop⟩
  have hr0 : r ≠ 0 := inv_ne_zero hPK0
  have hrc : ((r : ENNReal)) = (P K)⁻¹ := by
    rw [hr_def, ENNReal.coe_inv hPK0, ENNReal.coe_toNNReal hPKtop]
  have hQ : (P[|K]).join = r • (P.restrict K).join := by
    rw [ProbabilityTheory.cond, Measure.join_smul, ← hrc]
    rfl
  have hle0 : (P.restrict K).join ≤ P.join := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [Measure.join_apply hs, Measure.join_apply hs]
    exact setLIntegral_le_lintegral _ _
  have hle : (P[|K]).join ≤ r • P.join := by
    rw [hQ]
    refine Measure.le_iff.2 fun s hs => ?_
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    gcongr
  have hfinQ : IsFiniteMeasure (P[|K]).join := by
    constructor
    calc (P[|K]).join Set.univ ≤ (r • P.join) Set.univ := hle Set.univ
      _ < ⊤ := measure_lt_top _ _
  refine ⟨?_, ?_⟩
  · intro s hs
    have := hle s
    simp only [Measure.smul_apply, hs, smul_zero] at this
    exact le_zero_iff.1 this
  · have h1 : ∀ᵐ ω ∂(r • P.join), (P[|K]).join.rnDeriv (r • P.join) ω ≤ 1 :=
      Measure.rnDeriv_le_one_of_le hle
    rw [Measure.ae_smul_measure_iff hr0] at h1
    filter_upwards [h1, Measure.rnDeriv_smul_right (P[|K]).join P.join hr0] with ω hω hω'
    rw [hω'] at hω
    rw [← hrc]
    simp only [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] at hω
    rw [ENNReal.coe_inv hr0] at hω
    calc (P[|K]).join.rnDeriv P.join ω
        = (r : ENNReal) * ((r : ENNReal)⁻¹ * (P[|K]).join.rnDeriv P.join ω) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.2 hr0) ENNReal.coe_ne_top,
            one_mul]
      _ ≤ (r : ENNReal) * 1 := by gcongr
      _ = r := mul_one _
