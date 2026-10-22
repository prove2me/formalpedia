-- Prove2me | solution 1 for OnlineLearningOCO.NormalizedEG.eq_2_16_2_18
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:43:46.338639+00:00
-- url     : https://prove2.me/submissions/9f044795-69f2-4ffe-b547-71bd4bfa1ec3

import Mathlib
import Definitions.Def_OnlineLearningOCO_NormalizedEG_Duality
import Definitions.Def_UnderstandingML_Online

open OnlineLearningOCO.NormalizedEG UnderstandingML Finset

private lemma exp_sum_pos {d : ℕ} (hd : 0 < d) (v : Fin d → ℝ) :
    0 < ∑ i, Real.exp (v i) := by
  let i : Fin d := ⟨0,hd⟩
  exact (Real.exp_pos (v i)).trans_le
    (single_le_sum (fun j _ => (Real.exp_pos (v j)).le) (mem_univ i))

theorem solution {d : ℕ} (hd : 0 < d) (η : ℝ) (hη : 0 < η) (z : ℕ → Fin d → ℝ) (t : ℕ) :
    (∀ θ : Fin d → ℝ, HasFDerivAt (logSumExpConj η)
        (∑ i, softmaxEG η θ i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) i) θ) ∧
    softmaxEG η (-(cumSum z t)) = wmWeights η z t ∧
    bregmanLSE η (-(cumSum z (t + 1))) (-(cumSum z t)) =
      logSumExpConj η (-(cumSum z (t + 1))) - logSumExpConj η (-(cumSum z t)) +
        ∑ i, wmWeights η z t i * z t i ∧
    logSumExpConj η (-(cumSum z (t + 1))) - logSumExpConj η (-(cumSum z t)) +
        ∑ i, wmWeights η z t i * z t i =
      (1 / η) * Real.log ((∑ i, Real.exp (-η * cumSum z (t + 1) i)) /
          ∑ i, Real.exp (-η * cumSum z t i)) +
        ∑ i, wmWeights η z t i * z t i ∧
    (1 / η) * Real.log ((∑ i, Real.exp (-η * cumSum z (t + 1) i)) /
          ∑ i, Real.exp (-η * cumSum z t i)) +
        ∑ i, wmWeights η z t i * z t i =
      (1 / η) * Real.log (∑ i, wmWeights η z t i * Real.exp (-η * z t i)) +
        ∑ i, wmWeights η z t i * z t i := by
  classical
  have hc (n : ℕ) (i : Fin d) : cumSum z n i = ∑ r ∈ range n, z r i := by
    simp [cumSum]
  have hs (n : ℕ) : 0 < ∑ i, Real.exp (-η * cumSum z n i) :=
    exp_sum_pos hd _
  have hw : softmaxEG η (-(cumSum z t)) = wmWeights η z t := by
    ext i
    simp only [softmaxEG, wmWeights, Pi.neg_apply, mul_neg, neg_mul, hc]
  have hstep (i : Fin d) : cumSum z (t+1) i = cumSum z t i + z t i := by
    simp only [hc, sum_range_succ]
  refine ⟨?_, hw, ?_, ?_, ?_⟩
  · intro θ
    have hp := exp_sum_pos hd (fun i => η * θ i)
    have hf : HasFDerivAt (fun v : Fin d → ℝ => ∑ i, Real.exp (η * v i))
        (∑ i, Real.exp (η * θ i) •
          (η • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)) θ := by
      exact HasFDerivAt.fun_sum (fun i _ => ((hasFDerivAt_apply i θ).const_mul η).exp)
    have hl := (hf.log (ne_of_gt hp)).const_mul (1/η)
    have he : (1/η) • ((∑ i, Real.exp (η*θ i))⁻¹ •
        (∑ i, Real.exp (η*θ i) •
          (η • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i))) =
        ∑ i, softmaxEG η θ i •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i := by
      simp only [smul_sum, smul_smul]
      apply sum_congr rfl
      intro i _
      congr 1
      unfold softmaxEG
      field_simp
      <;> ring
    rw [he] at hl
    exact hl
  · unfold bregmanLSE
    rw [hw]
    have hdot : (∑ i, wmWeights η z t i *
        ((-(cumSum z (t+1))) i - (-(cumSum z t)) i)) =
        -(∑ i, wmWeights η z t i * z t i) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro i _
      simp only [Pi.neg_apply, hstep]
      ring
    rw [hdot]
    ring
  · simp only [logSumExpConj, Pi.neg_apply, mul_neg, ← neg_mul]
    rw [Real.log_div (ne_of_gt (hs (t+1))) (ne_of_gt (hs t))]
    ring
  · have hr : ((∑ i, Real.exp (-η * cumSum z (t+1) i)) /
        ∑ i, Real.exp (-η * cumSum z t i)) =
        ∑ i, wmWeights η z t i * Real.exp (-η * z t i) := by
      rw [sum_div]
      apply sum_congr rfl
      intro i _
      rw [hstep, mul_add, Real.exp_add]
      simp only [wmWeights, hc]
      ring
    rw [hr]
