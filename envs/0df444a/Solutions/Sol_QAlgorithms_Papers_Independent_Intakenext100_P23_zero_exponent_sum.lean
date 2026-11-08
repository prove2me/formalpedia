-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P23.zero_exponent_sum
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:46:30.103231+00:00
-- url     : https://prove2.me/submissions/9bc10d71-0f8a-45ba-8347-f1fc6e0c83dc

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P23

noncomputable section

open scoped BigOperators Topology

open Filter Set MeasureTheory

namespace Aux_P23zero

lemma gauss (m : ℕ) : ∑ i ∈ Finset.range m, (((i + 1 : ℕ) : ℝ)) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

end Aux_P23zero

open QAlgorithms.Papers.Independent.Intakenext100.P23 in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    replicaP n 0 = ((n : ℝ) - 1) / 2 ∧
    HasDerivAt zeroPContinuation (1 / 2) 1 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m + 1 - 1 = m := by omega
    unfold replicaP
    simp only [mul_zero, Real.rpow_zero, div_one]
    rw [Fin.sum_univ_eq_sum_range (fun l => ((l + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) (m + 1 - 1),
      hm, ← Finset.sum_div, Aux_P23zero.gauss]
    push_cast
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    field_simp <;> ring
  · show HasDerivAt (fun n : ℝ => (n - 1) / 2) (1 / 2) 1
    exact ((hasDerivAt_id' (1 : ℝ)).sub_const 1).div_const 2
