-- Prove2me | solution 1 for SharingPlatform.WageSchemes.price_dcr_vs_fw
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:26:11.566892+00:00
-- url     : https://prove2.me/submissions/19ee3176-132e-4929-95a7-d774204edc0d

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model

open SharingPlatform.WageSchemes

theorem solution (P : Params) (hP : P.Standing) :
    pW P - pD P =
      P.b * P.m * (P.l + P.m) * (P.a * P.m - P.c * P.k) * (P.b * P.m - P.c * P.l) /
        (P.c * (P.b * (P.c * (P.l + 2 * P.m) + P.m * (P.l + P.m)) +
            P.c * (P.c * (P.l + 2 * P.m) + 2 * P.m * (P.l + P.m))) *
          (P.b * (2 * P.c * (P.l + 2 * P.m) + P.m * (2 * P.l + 3 * P.m)) +
            P.c * (P.c * (P.l + 2 * P.m) + 2 * P.m * (P.l + P.m)))) ∧
    (pD P ≤ pW P ↔ P.c * P.l ≤ P.b * P.m) ∧
    (pD P < pW P ↔ P.c * P.l < P.b * P.m) := by
  obtain ⟨a, b, c, k, l, m⟩ := P
  obtain ⟨ha, hb, hc, hk, hl, hm, hA1, hA2⟩ := hP
  dsimp only at ha hb hc hk hl hm hA1 hA2
  simp only [pW, wW, pD]
  have ham : 0 < a * m - c * k := by
    rw [div_lt_div_iff₀ hm hc] at hA1; linarith
  have hD1 : 0 < b * (c * (l + 2 * m) + m * (l + m)) + c * (c * (l + 2 * m) + 2 * m * (l + m)) := by
    positivity
  have hD2 : 0 < b * (2 * c * (l + 2 * m) + m * (2 * l + 3 * m)) +
      c * (c * (l + 2 * m) + 2 * m * (l + m)) := by positivity
  have hDp : 0 < c * (b + c) * (l + 2 * m) + m * (b + 2 * c) * (l + m) := by positivity
  have hid : (a + k - m * ((b * (2 * a * (l + m) + 2 * c * k + k * (2 * l + 3 * m)) +
      c * ((a + 2 * k) * (l + m) + c * k)) /
    (b * (2 * c * (l + 2 * m) + m * (2 * l + 3 * m)) +
      c * (c * (l + 2 * m) + 2 * m * (l + m))))) / c -
      (k * (b + c) * (l + m) + a * (m * (l + m) + (b + c) * (l + 2 * m))) /
        (c * (b + c) * (l + 2 * m) + m * (b + 2 * c) * (l + m)) =
      b * m * (l + m) * (a * m - c * k) * (b * m - c * l) /
        (c * (b * (c * (l + 2 * m) + m * (l + m)) +
            c * (c * (l + 2 * m) + 2 * m * (l + m))) *
          (b * (2 * c * (l + 2 * m) + m * (2 * l + 3 * m)) +
            c * (c * (l + 2 * m) + 2 * m * (l + m)))) := by
    rw [eq_div_iff (by positivity)]
    field_simp
    ring
  have hpos : 0 < c * (b * (c * (l + 2 * m) + m * (l + m)) +
            c * (c * (l + 2 * m) + 2 * m * (l + m))) *
          (b * (2 * c * (l + 2 * m) + m * (2 * l + 3 * m)) +
            c * (c * (l + 2 * m) + 2 * m * (l + m))) := by positivity
  have hK : 0 < b * m * (l + m) * (a * m - c * k) := by positivity
  refine ⟨hid, ?_, ?_⟩
  · rw [← sub_nonneg, hid, div_nonneg_iff]
    constructor
    · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · have : 0 ≤ b * m - c * l := by
          by_contra hcon; push_neg at hcon; nlinarith
        linarith
      · linarith
    · intro h; left; exact ⟨mul_nonneg hK.le (by linarith), hpos.le⟩
  · rw [← sub_pos, hid, div_pos_iff_of_pos_right hpos]
    constructor
    · intro h
      by_contra hcon; push_neg at hcon; nlinarith
    · intro h; exact mul_pos hK (by linarith)
