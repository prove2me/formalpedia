-- Prove2me | solution 1 for OnlineLearningOCO.NormalizedEG.bregman_step_bound
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:45:05.446637+00:00
-- url     : https://prove2.me/submissions/2065cec1-44db-4938-a33e-b342fab33073

import Mathlib
import Definitions.Def_OnlineLearningOCO_NormalizedEG_Duality
import Definitions.Def_UnderstandingML_Online
import Theorems.Thm_OnlineLearningOCO_NormalizedEG_eq_2_16_2_18

open OnlineLearningOCO.NormalizedEG UnderstandingML Finset

private lemma exp_quadratic (a : ℝ) (ha : a ≤ 1) : Real.exp a ≤ 1+a+a^2 := by
  by_cases hlo : -1 ≤ a
  · have hab : ‖a‖ ≤ 1 := by simpa only [Real.norm_eq_abs, abs_le] using And.intro hlo ha
    have hb := Real.norm_exp_sub_one_sub_id_le hab
    simp only [Real.norm_eq_abs, sq_abs] at hb
    have hu := (abs_le.mp hb).2
    linarith
  · have he : Real.exp a ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [sq_nonneg (a+1)]

private lemma sum_exp_pos {d : ℕ} (hd : 0 < d) (v : Fin d → ℝ) :
    0 < ∑ i, Real.exp (v i) := by
  let i : Fin d := ⟨0,hd⟩
  exact (Real.exp_pos (v i)).trans_le
    (single_le_sum (fun j _ => (Real.exp_pos (v j)).le) (mem_univ i))

theorem solution {d : ℕ} (hd : 0 < d) (η : ℝ) (hη : 0 < η) (z : ℕ → Fin d → ℝ) (t : ℕ)
    (hz : ∀ i, -1 ≤ η * z t i) :
    bregmanLSE η (-(cumSum z (t + 1))) (-(cumSum z t)) ≤
      η * ∑ i, wmWeights η z t i * z t i ^ 2 := by
  classical
  have hd0 := sum_exp_pos hd (fun i => -η * ∑ r ∈ range t, z r i)
  have hw (i : Fin d) : 0 < wmWeights η z t i := div_pos (Real.exp_pos _) hd0
  have hw1 : ∑ i, wmWeights η z t i = 1 := by
    unfold wmWeights
    rw [← sum_div, div_self (ne_of_gt hd0)]
  let A := ∑ i, wmWeights η z t i * Real.exp (-η * z t i)
  have hA : 0 < A := by
    let i : Fin d := ⟨0,hd⟩
    exact (mul_pos (hw i) (Real.exp_pos _)).trans_le
      (single_le_sum (fun j _ => (mul_pos (hw j) (Real.exp_pos _)).le) (mem_univ i))
  have hbound : A ≤ 1 - η * (∑ i, wmWeights η z t i * z t i) +
      η^2 * (∑ i, wmWeights η z t i * z t i^2) := by
    have hh : A ≤ ∑ i, wmWeights η z t i * (1 - η*z t i + η^2*z t i^2) := by
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i).le
      have h := exp_quadratic (-η*z t i) (by have := hz i; nlinarith)
      nlinarith
    have he : (∑ i, wmWeights η z t i * (1 - η*z t i + η^2*z t i^2)) =
        1 - η * (∑ i, wmWeights η z t i * z t i) +
        η^2 * (∑ i, wmWeights η z t i * z t i^2) := by
      calc
        _ = (∑ i, wmWeights η z t i) - η * (∑ i, wmWeights η z t i * z t i) +
            η^2 * (∑ i, wmWeights η z t i * z t i^2) := by
          simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
          apply sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [hw1]
    exact he ▸ hh
  have hlog := Real.log_le_sub_one_of_pos hA
  have hscaled := mul_le_mul_of_nonneg_left (hlog.trans (sub_le_sub_right hbound 1))
    (le_of_lt (one_div_pos.mpr hη))
  have hid := eq_2_16_2_18 hd η hη z t
  rw [hid.2.2.1, hid.2.2.2.1, hid.2.2.2.2]
  change (1/η)*Real.log A + _ ≤ _
  have he : (1/η) * ((1 - η*(∑ i, wmWeights η z t i*z t i) +
      η^2*(∑ i, wmWeights η z t i*z t i^2))-1) =
      -(∑ i, wmWeights η z t i*z t i) + η*(∑ i, wmWeights η z t i*z t i^2) := by
    field_simp
    <;> ring
  rw [he] at hscaled
  linarith
