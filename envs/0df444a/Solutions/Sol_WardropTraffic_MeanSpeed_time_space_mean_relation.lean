-- Prove2me | solution 1 for WardropTraffic.MeanSpeed.time_space_mean_relation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:04:23.01572+00:00
-- url     : https://prove2.me/submissions/85e2b48e-b5fc-4aa4-b60d-5b245b71d386

import Mathlib
import Definitions.Def_WardropTraffic_MeanSpeed_Setting



namespace WardropTraffic.MeanSpeed

theorem ms_conc {C : ℕ} (q v : Fin C → ℝ) (hv : ∀ i, 0 < v i) (i : Fin C) :
    conc q v i * v i = q i := by
  unfold conc; have := (hv i).ne'; field_simp

theorem ms_conc_pos {C : ℕ} (q v : Fin C → ℝ) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) (i : Fin C) :
    0 < conc q v i := by
  unfold conc; exact div_pos (hq i) (hv i)

theorem ms_K_pos {C : ℕ} (q v : Fin C → ℝ) (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    0 < totalConc q v := by
  unfold totalConc
  haveI : Nonempty (Fin C) := ⟨⟨0, hC⟩⟩
  exact Finset.sum_pos (fun i _ => ms_conc_pos q v hq hv i) Finset.univ_nonempty

theorem ms_Q_pos {C : ℕ} (q : Fin C → ℝ) (hC : 0 < C) (hq : ∀ i, 0 < q i) :
    0 < totalFlow q := by
  unfold totalFlow
  haveI : Nonempty (Fin C) := ⟨⟨0, hC⟩⟩
  exact Finset.sum_pos (fun i _ => hq i) Finset.univ_nonempty

theorem ms_sumcv {C : ℕ} (q v : Fin C → ℝ) (hv : ∀ i, 0 < v i) :
    ∑ i, conc q v i * v i = totalFlow q := by
  unfold totalFlow
  exact Finset.sum_congr rfl (fun i _ => ms_conc q v hv i)

theorem ms_Q_eq {C : ℕ} (q v : Fin C → ℝ) (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    totalFlow q = totalConc q v * spaceMean q v := by
  have hK := (ms_K_pos q v hC hq hv).ne'
  unfold spaceMean
  rw [ms_sumcv q v hv]; field_simp

theorem ms_sumcv2 {C : ℕ} (q v : Fin C → ℝ) (hv : ∀ i, 0 < v i) :
    ∑ i, conc q v i * v i ^ 2 = ∑ i, q i * v i := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← ms_conc q v hv i]; ring

theorem ms_var {C : ℕ} (q v : Fin C → ℝ) (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    spaceVar q v = (∑ i, q i * v i) / totalConc q v - spaceMean q v ^ 2 := by
  have hK := (ms_K_pos q v hC hq hv).ne'
  have hm : ∑ i, conc q v i * v i = spaceMean q v * totalConc q v := by
    unfold spaceMean; field_simp
  have h1 : ∑ i, conc q v i * (v i - spaceMean q v) ^ 2
      = (∑ i, q i * v i) - 2 * spaceMean q v * (∑ i, conc q v i * v i)
        + spaceMean q v ^ 2 * totalConc q v := by
    unfold totalConc
    rw [Finset.mul_sum, Finset.mul_sum, ← ms_sumcv2 q v hv]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  unfold spaceVar
  rw [h1, hm]; field_simp; ring

theorem ms_flow_concentration {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    (∀ i, conc q v i * v i = q i) ∧
      totalFlow q = totalConc q v * spaceMean q v :=
  ⟨ms_conc q v hv, ms_Q_eq q v hC hq hv⟩

theorem ms_space_frequencies {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    (∑ i, spaceFreq q v i * (v i - spaceMean q v)) = 0 := by
  have hK := (ms_K_pos q v hC hq hv).ne'
  have hm : ∑ i, conc q v i * v i = spaceMean q v * totalConc q v := by
    unfold spaceMean; field_simp
  have : ∑ i, spaceFreq q v i * (v i - spaceMean q v)
      = (∑ i, conc q v i * v i - spaceMean q v * totalConc q v) / totalConc q v := by
    unfold spaceFreq totalConc
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [this, hm]; simp

theorem ms_time_mean_second_moment {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    timeMean q v = (∑ i, spaceFreq q v i * v i ^ 2) / spaceMean q v := by
  have hK := (ms_K_pos q v hC hq hv).ne'
  have hQ := (ms_Q_pos q hC hq).ne'
  have hQe := ms_Q_eq q v hC hq hv
  have hm : spaceMean q v ≠ 0 := by
    intro h; rw [h, mul_zero] at hQe; exact hQ hQe
  have : ∑ i, spaceFreq q v i * v i ^ 2 = (∑ i, q i * v i) / totalConc q v := by
    rw [← ms_sumcv2 q v hv, Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by unfold spaceFreq; ring)
  rw [this]; unfold timeMean
  rw [hQe]; field_simp

theorem ms_core {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    timeMean q v = spaceMean q v + spaceVar q v / spaceMean q v ∧
      spaceMean q v ≤ timeMean q v ∧
      (timeMean q v = spaceMean q v ↔ ∀ i j, v i = v j) := by
  have hK := ms_K_pos q v hC hq hv
  have hQ := ms_Q_pos q hC hq
  have hQe := ms_Q_eq q v hC hq hv
  have hm0 : 0 < spaceMean q v := by
    by_contra h; push_neg at h
    have : totalConc q v * spaceMean q v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK.le h
    linarith
  have hvar := ms_var q v hC hq hv
  have h1 : timeMean q v = spaceMean q v + spaceVar q v / spaceMean q v := by
    unfold timeMean
    rw [hvar]
    have hs : (∑ i, q i * v i) / totalConc q v = (∑ i, q i * v i) / totalFlow q * spaceMean q v := by
      rw [hQe]; field_simp
    rw [hs]; field_simp; ring
  have hvnn : 0 ≤ spaceVar q v := by
    unfold spaceVar
    refine div_nonneg (Finset.sum_nonneg fun i _ => ?_) hK.le
    exact mul_nonneg (ms_conc_pos q v hq hv i).le (sq_nonneg _)
  refine ⟨h1, ?_, ?_⟩
  · rw [h1]; have := div_nonneg hvnn hm0.le; linarith
  · constructor
    · intro h
      have h0 : spaceVar q v / spaceMean q v = 0 := by linarith
      have h2 : spaceVar q v = 0 := by
        rcases div_eq_zero_iff.mp h0 with h | h
        · exact h
        · exact absurd h hm0.ne'
      unfold spaceVar at h2
      have h3 : ∑ i, conc q v i * (v i - spaceMean q v) ^ 2 = 0 := by
        rcases div_eq_zero_iff.mp h2 with h | h
        · exact h
        · exact absurd h hK.ne'
      have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
        mul_nonneg (ms_conc_pos q v hq hv i).le (sq_nonneg _))).mp h3
      have h5 : ∀ i, v i = spaceMean q v := by
        intro i
        have := h4 i (Finset.mem_univ i)
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (ms_conc_pos q v hq hv i).ne'
        · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
          linarith
      intro i j; rw [h5 i, h5 j]
    · intro h
      have hm : spaceMean q v = v ⟨0, hC⟩ := by
        unfold spaceMean
        have : ∑ i, conc q v i * v i = v ⟨0, hC⟩ * totalConc q v := by
          unfold totalConc; rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by rw [h i ⟨0, hC⟩]; ring)
        rw [this]; field_simp
      have hv0 : spaceVar q v = 0 := by
        unfold spaceVar
        have : ∑ i, conc q v i * (v i - spaceMean q v) ^ 2 = 0 :=
          Finset.sum_eq_zero (fun i _ => by rw [hm, h i ⟨0, hC⟩]; simp)
        rw [this]; simp
      rw [h1, hv0]; simp

end WardropTraffic.MeanSpeed

open WardropTraffic.MeanSpeed


theorem solution {C : ℕ} (q v : Fin C → ℝ)
    (hC : 0 < C) (hq : ∀ i, 0 < q i) (hv : ∀ i, 0 < v i) :
    timeMean q v = spaceMean q v + spaceVar q v / spaceMean q v ∧
      spaceMean q v ≤ timeMean q v ∧
      (timeMean q v = spaceMean q v ↔ ∀ i j, v i = v j) := by
  exact ms_core q v hC hq hv
