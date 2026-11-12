-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P64.decoherence_exponentCrossover
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:42:40.062196+00:00
-- url     : https://prove2.me/submissions/1adc59e1-76c6-4b7b-bcbd-05f63baf37e0

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P64

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal NNReal Topology

open QAlgorithms.Papers.Independent.Claimed50.P39 (rising)

open QAlgorithms.Papers.Independent.Intake100.P64 in
theorem solution (M beta hbar eta t : ℝ)
    (hM : 0 < M) (hbeta : 0 < beta) (hhbar : 0 < hbar) (heta : 0 < eta)
    (ht : 0 < t) (delta : Momentum) (hdelta : delta ≠ 0) :
    dispersionExponent M beta hbar eta t delta / quantumExponent M beta eta t delta =
      4 / 3 * (t / (beta * hbar)) ^ 2 ∧
    (quantumExponent M beta eta t delta ≤ dispersionExponent M beta hbar eta t delta ↔
      Real.sqrt 3 * beta * hbar / 2 ≤ t) := by
  have hd : 0 < ‖delta‖ := norm_pos_iff.2 hdelta
  have hd' : ‖delta‖ ≠ 0 := hd.ne'
  have hM' := hM.ne'
  have hb' := hbeta.ne'
  have hh' := hhbar.ne'
  have he' := heta.ne'
  have ht' := ht.ne'
  have hQ : 0 < quantumExponent M beta eta t delta := by
    unfold quantumExponent
    positivity
  have h1 : dispersionExponent M beta hbar eta t delta / quantumExponent M beta eta t delta =
      4 / 3 * (t / (beta * hbar)) ^ 2 := by
    unfold dispersionExponent quantumExponent
    field_simp <;> ring
  refine ⟨h1, ?_⟩
  have hD : dispersionExponent M beta hbar eta t delta =
      4 / 3 * (t / (beta * hbar)) ^ 2 * quantumExponent M beta eta t delta := by
    rw [← h1, div_mul_cancel₀ _ hQ.ne']
  have hs : 0 < beta * hbar := mul_pos hbeta hhbar
  have hrew : 4 / 3 * (t / (beta * hbar)) ^ 2 = (4 * t ^ 2) / (3 * (beta * hbar) ^ 2) := by
    ring
  have hX : (Real.sqrt 3 * beta * hbar / 2) * (Real.sqrt 3 * beta * hbar / 2) =
      3 * (beta * hbar) ^ 2 / 4 := by
    rw [show (Real.sqrt 3 * beta * hbar / 2) * (Real.sqrt 3 * beta * hbar / 2) =
      (Real.sqrt 3 * Real.sqrt 3) * (beta * hbar) ^ 2 / 4 by ring,
      Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hX0 : 0 ≤ Real.sqrt 3 * beta * hbar / 2 := by positivity
  rw [hD, le_mul_iff_one_le_left hQ, hrew, le_div_iff₀ (show (0:ℝ) < 3 * (beta * hbar) ^ 2 by positivity)]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have := mul_self_lt_mul_self ht.le hc
    nlinarith
  · intro hc
    have := mul_self_le_mul_self hX0 hc
    nlinarith

end
