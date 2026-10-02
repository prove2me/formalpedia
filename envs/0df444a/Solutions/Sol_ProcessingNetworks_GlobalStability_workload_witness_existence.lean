-- Prove2me | solution 1 for ProcessingNetworks.GlobalStability.workload_witness_existence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T01:36:16.301358+00:00
-- url     : https://prove2.me/submissions/e155afe2-55b6-4f60-a7d9-5159c6387727

import Mathlib

private theorem exists_between4 (a b c d : ℝ) (hac : a < c) (had : a < d) (hbc : b < c)
    (hbd : b < d) : ∃ x : ℝ, a < x ∧ b < x ∧ x < c ∧ x < d := by
  have h2 : max a b < min c d := max_lt (lt_min hac had) (lt_min hbc hbd)
  refine ⟨(max a b + min c d) / 2, ?_, ?_, ?_, ?_⟩
  · have := le_max_left a b; linarith
  · have := le_max_right a b; linarith
  · have := min_le_left c d; linarith
  · have := min_le_right c d; linarith

private theorem exists_between3 (a c d : ℝ) (hac : a < c) (had : a < d) :
    ∃ x : ℝ, a < x ∧ x < c ∧ x < d := by
  have h2 : a < min c d := lt_min hac had
  refine ⟨(a + min c d) / 2, ?_, ?_, ?_⟩
  · linarith
  · have := min_le_left c d; linarith
  · have := min_le_right c d; linarith

private theorem exists_pos_le5 (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) :
    ∃ x : ℝ, 0 < x ∧ x ≤ a ∧ x ≤ b ∧ x ≤ c ∧ x ≤ d ∧ x ≤ e := by
  refine ⟨min a (min b (min c (min d e))), lt_min ha (lt_min hb (lt_min hc (lt_min hd he))),
    min_le_left _ _, ?_, ?_, ?_, ?_⟩
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  · exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  · exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))

theorem solution
    (lam1 m1 m2 m3 m4 m5 : ℝ) (hlam1 : 0 < lam1)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm3 : 0 < m3) (hm4 : 0 < m4) (hm5 : 0 < m5)
    (h47 : lam1 * (m1 + m3 + m5) < 1) (h48 : lam1 * (m2 + m4) < 1) (h49 : lam1 * (m2 + m5) < 1) :
    ∃ x1 x2 x3 x4 x5 ε : ℝ, 0 < x1 ∧ 0 < x2 ∧ 0 < x3 ∧ 0 < x4 ∧ 0 < x5 ∧ 0 < ε ∧
      lam1 * (x2 + x4) + ε ≤ x2 / m2 ∧ lam1 * (x2 + x4) + ε ≤ x4 / m4 ∧
      lam1 * (x1 + x3 + x5) + ε ≤ x1 / m1 ∧ lam1 * (x1 + x3 + x5) + ε ≤ x3 / m3 ∧
      lam1 * (x1 + x3 + x5) + ε ≤ x5 / m5 ∧
      x2 + x4 ≤ x1 + x3 + x5 ∧ x4 ≤ x3 + x5 ∧
      x3 + x5 ≤ x2 + x4 ∧ x5 ≤ x4 := by
  -- normalised loads
  set P := lam1 * m1 with hPdef
  set Q := lam1 * m3 with hQdef
  set R := lam1 * m5 with hRdef
  set S := lam1 * m2 with hSdef
  set U := lam1 * m4 with hUdef
  have hP : 0 < P := by rw [hPdef]; positivity
  have hQ : 0 < Q := by rw [hQdef]; positivity
  have hR : 0 < R := by rw [hRdef]; positivity
  have hS : 0 < S := by rw [hSdef]; positivity
  have hU : 0 < U := by rw [hUdef]; positivity
  have hPQR : P + Q + R < 1 := by rw [hPdef, hQdef, hRdef]; nlinarith [h47]
  have hSU : S + U < 1 := by rw [hSdef, hUdef]; nlinarith [h48]
  have hSR : S + R < 1 := by rw [hSdef, hRdef]; nlinarith [h49]
  have h1S : (0 : ℝ) < 1 - S := by linarith
  have hUlt : U < 1 - S := by linarith
  have hU1 : U < 1 := by linarith
  -- Step 1: choose V
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ :
      ∃ V : ℝ, Q + R < V ∧ R / (1 - S) < V ∧ V < 1 ∧ V < (1 - P) / U := by
    refine exists_between4 _ _ _ _ (by linarith) ?_ ?_ ?_
    · rw [lt_div_iff₀ hU]; nlinarith
    · rw [div_lt_one h1S]; linarith
    · rw [div_lt_div_iff₀ h1S hU]; nlinarith
  have hVpos : 0 < V := by linarith
  have hUV : U * V < 1 - P := by
    have := (lt_div_iff₀ hU).mp hV4
    linarith [this]
  have hRV : R < (1 - S) * V := by
    have := (div_lt_iff₀ h1S).mp hV2
    linarith [this]
  -- Step 2: choose Y
  obtain ⟨Y, hY1, hY2, hY3, hY4⟩ :
      ∃ Y : ℝ, Q + R < Y ∧ U * V < Y ∧ Y < V ∧ Y < 1 - P := by
    refine exists_between4 _ _ _ _ hV1 (by linarith) ?_ hUV
    nlinarith
  -- Step 3: choose x4
  obtain ⟨X4, hX41, hX42, hX43, hX44⟩ :
      ∃ X4 : ℝ, U * V < X4 ∧ R < X4 ∧ X4 < Y ∧ X4 < (1 - S) * V := by
    refine exists_between4 _ _ _ _ hY2 ?_ (by linarith) hRV
    nlinarith
  -- Step 4: choose x5
  obtain ⟨X5, hX51, hX52, hX53⟩ : ∃ X5 : ℝ, R < X5 ∧ X5 < X4 ∧ X5 < Y - Q := by
    exact exists_between3 _ _ _ hX42 (by linarith)
  -- the five slacks are positive
  have g1 : 0 < (V - X4) / m2 - lam1 * V := by
    have : lam1 * V * m2 < V - X4 := by rw [hSdef] at hX44; nlinarith
    have h := (lt_div_iff₀ hm2).mpr this
    linarith
  have g2 : 0 < X4 / m4 - lam1 * V := by
    have : lam1 * V * m4 < X4 := by rw [hUdef] at hX41; nlinarith
    have h := (lt_div_iff₀ hm4).mpr this
    linarith
  have g3 : 0 < (1 - Y) / m1 - lam1 := by
    have : lam1 * m1 < 1 - Y := by rw [← hPdef]; linarith
    have h := (lt_div_iff₀ hm1).mpr this
    linarith
  have g4 : 0 < (Y - X5) / m3 - lam1 := by
    have : lam1 * m3 < Y - X5 := by rw [← hQdef]; linarith
    have h := (lt_div_iff₀ hm3).mpr this
    linarith
  have g5 : 0 < X5 / m5 - lam1 := by
    have : lam1 * m5 < X5 := by rw [← hRdef]; linarith
    have h := (lt_div_iff₀ hm5).mpr this
    linarith
  obtain ⟨ε, hε0, he1, he2, he3, he4, he5⟩ :=
    exists_pos_le5 _ _ _ _ _ g1 g2 g3 g4 g5
  -- positivity of the coordinates
  have hx1 : 0 < 1 - Y := by linarith
  have hx2 : 0 < V - X4 := by nlinarith
  have hx3 : 0 < Y - X5 := by linarith
  refine ⟨1 - Y, V - X4, Y - X5, X4, X5, ε, hx1, hx2, hx3, by linarith, by linarith, hε0,
    by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩
