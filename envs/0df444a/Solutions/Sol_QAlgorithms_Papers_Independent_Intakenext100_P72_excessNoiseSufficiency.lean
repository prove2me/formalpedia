-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P72.excessNoiseSufficiency
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T10:11:32.572198+00:00
-- url     : https://prove2.me/submissions/74e104ee-0f28-41bd-94cd-66048869a713

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P72

noncomputable section

open Filter

open scoped Topology

open QAlgorithms.Papers.Independent.Intakenext100.P72 in
theorem solution
    (G V excess : ℝ) (hG : 0 < G) (hGloss : G ≤ 1)
    (hV : 1 ≤ V) (hexcess : 0 ≤ excess) :
    (excess < coherentExcessThreshold V →
      0 < coherentExpression G ((1 - G) / G + excess) V) ∧
    (excess < eprExcessThreshold V →
      0 < eprExpression G ((1 - G) / G + excess) V) ∧
    Tendsto coherentExcessThreshold atTop (nhds (1 / 2 : ℝ)) ∧
    Tendsto eprExcessThreshold atTop (nhds (1 : ℝ)) := by
  have hV0 : 0 < V := by linarith
  have hGne := hG.ne'
  have hVne := hV0.ne'
  obtain ⟨t, htd⟩ : ∃ t, t = 1 / V := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htd]; exact div_pos one_pos hV0
  have ht1 : t ≤ 1 := by rw [htd, div_le_one hV0]; exact hV
  have hGc : G * ((1 - G) / G + excess) = 1 - G + G * excess := by
    field_simp <;> ring
  have hGV : G / V = G * t := by rw [htd]; ring
  have hcth : coherentExcessThreshold V = (1 - t) / 2 := by
    unfold coherentExcessThreshold; rw [htd]; field_simp <;> ring
  have heth : eprExcessThreshold V = 1 - t := by
    unfold eprExcessThreshold; rw [htd]; field_simp <;> ring
  have hlog : ∀ P : ℝ, 0 < P → P < 1 → 0 < Real.logb 2 (1 / P) := fun P h0 h1 =>
    Real.logb_pos (by norm_num) (one_lt_one_div h0 h1)
  refine ⟨fun he => ?_, fun he => ?_, ?_, ?_⟩
  · rw [hcth] at he
    unfold coherentExpression balanceExpression varianceProduct
    rw [hGc, hGV, mul_one]
    have hA : 0 < 1 - G + G * excess + G := by nlinarith [mul_nonneg hG.le hexcess]
    have hB : 0 < 1 - G + G * excess + G * t := by
      nlinarith [mul_nonneg hG.le hexcess, mul_pos hG ht0]
    have hP0 : 0 < (1 - G + G * excess + G) * (1 - G + G * excess + G * t) := mul_pos hA hB
    have hP1 : (1 - G + G * excess + G) * (1 - G + G * excess + G * t) < 1 := by
      have k1 : 0 < G * (1 - t - 2 * excess) := mul_pos hG (by linarith)
      have k2 : 0 ≤ G * G * excess * (1 - t - excess) :=
        mul_nonneg (mul_nonneg (mul_nonneg hG.le hG.le) hexcess) (by linarith)
      nlinarith
    have := hlog _ hP0 hP1
    exact mul_pos (by norm_num) this
  · rw [heth] at he
    unfold eprExpression balanceExpression varianceProduct
    rw [hGc, hGV]
    have hB : 0 < 1 - G + G * excess + G * t := by
      nlinarith [mul_nonneg hG.le hexcess, mul_pos hG ht0]
    have hBlt : 1 - G + G * excess + G * t < 1 := by
      have := mul_pos hG (by linarith : (0 : ℝ) < 1 - t - excess)
      nlinarith
    have hP0 : 0 < (1 - G + G * excess + G * (1 / V)) * (1 - G + G * excess + G * t) := by
      rw [← htd]; exact mul_pos hB hB
    have hP1 : (1 - G + G * excess + G * (1 / V)) * (1 - G + G * excess + G * t) < 1 := by
      rw [← htd]; nlinarith [mul_lt_mul_of_pos_left hBlt hB]
    have := hlog _ hP0 hP1
    exact mul_pos (by norm_num) (mul_pos (by norm_num) this)
  · have h : Tendsto (fun V : ℝ => (1 : ℝ) / 2 - 1 / 2 * V⁻¹) atTop (nhds (1 / 2 - 1 / 2 * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_atTop_zero)
    rw [show (1 : ℝ) / 2 - 1 / 2 * 0 = 1 / 2 by ring] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with W hW
    have := hW.ne'
    unfold coherentExcessThreshold
    field_simp <;> ring
  · have h : Tendsto (fun V : ℝ => (1 : ℝ) - V⁻¹) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub tendsto_inv_atTop_zero
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with W hW
    have := hW.ne'
    unfold eprExcessThreshold
    field_simp <;> ring

end
