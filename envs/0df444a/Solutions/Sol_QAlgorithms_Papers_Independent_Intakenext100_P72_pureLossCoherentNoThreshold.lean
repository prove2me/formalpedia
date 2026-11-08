-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P72.pureLossCoherentNoThreshold
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:57:19.662397+00:00
-- url     : https://prove2.me/submissions/1777d0f6-c95f-49ee-a5f0-48409f15ba63

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P72

noncomputable section

open Filter

open scoped Topology

open QAlgorithms.Papers.Independent.Intakenext100.P72 in
theorem solution
    (G V : ℝ) (hG : 0 < G) (hGloss : G ≤ 1) (hV : 1 < V) :
    1 - G < noiseThreshold G 1 ∧
    varianceProduct G ((1 - G) / G) V 1 < 1 ∧
    0 < coherentExpression G ((1 - G) / G) V ∧
    coherentExpression G ((1 - G) / G) V = eprExpression G ((1 - G) / G) V ∧
    coherentExpression G ((1 - G) / G) V = lossExpression G V := by
  have hV0 : 0 < V := by linarith
  have hGne : G ≠ 0 := hG.ne'
  have hVne : V ≠ 0 := hV0.ne'
  have hP1 : varianceProduct G ((1 - G) / G) V 1 = 1 - G * (1 - 1 / V) := by
    unfold varianceProduct
    field_simp <;> ring
  have hP2 : varianceProduct G ((1 - G) / G) V (1 / V) = (1 - G * (1 - 1 / V)) ^ 2 := by
    unfold varianceProduct
    field_simp <;> ring
  have hiv : 1 / V < 1 := by rw [div_lt_one hV0]; exact hV
  have hiv0 : 0 < 1 / V := by positivity
  have hPpos : 0 < 1 - G * (1 - 1 / V) := by nlinarith
  have hPlt : 1 - G * (1 - 1 / V) < 1 := by nlinarith
  have hlog : 0 < Real.logb 2 (1 / (1 - G * (1 - 1 / V))) := by
    apply Real.logb_pos (by norm_num)
    rw [lt_div_iff₀ hPpos]; linarith
  have hcoh : coherentExpression G ((1 - G) / G) V
      = (1 / 2 : ℝ) * Real.logb 2 (1 / (1 - G * (1 - 1 / V))) := by
    unfold coherentExpression balanceExpression
    rw [hP1]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold noiseThreshold
    simp only [one_pow, mul_one]
    have hs : 2 - G < Real.sqrt (G ^ 2 + 4) := by
      rcases le_or_gt (2 - G) 0 with h | h
      · exact lt_of_le_of_lt h (Real.sqrt_pos.mpr (by positivity))
      · rw [Real.lt_sqrt h.le]; nlinarith
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  · rw [hP1]; exact hPlt
  · rw [hcoh]; positivity
  · rw [hcoh]
    unfold eprExpression balanceExpression
    rw [hP2, ← one_div_pow, Real.logb_pow]
    push_cast
    ring
  · rw [hcoh]
    rfl
